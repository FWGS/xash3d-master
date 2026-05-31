use std::{
    cell::UnsafeCell,
    fmt::{self, Write},
    mem::ManuallyDrop,
    sync::{
        atomic::{AtomicI64, AtomicU64, Ordering},
        Once, OnceLock, RwLock,
    },
};

/// A cumulative metric that represents a single monotonically increasing counter.
///
/// See [Counter](https://prometheus.io/docs/concepts/metric_types/#counter).
pub struct Counter {
    value: AtomicU64,
}

impl Counter {
    #[inline(always)]
    const fn new() -> Self {
        Self {
            value: AtomicU64::new(0),
        }
    }

    #[inline(always)]
    pub fn get(&self) -> u64 {
        self.value.load(Ordering::Relaxed)
    }

    #[inline(always)]
    pub fn add(&self, value: u64) {
        self.value.fetch_add(value, Ordering::Relaxed);
    }

    #[inline(always)]
    pub fn inc(&self) {
        self.add(1)
    }
}

/// A metric that represents a single numerical value that can arbitrarily go up and down.
///
/// See [Gauge](https://prometheus.io/docs/concepts/metric_types/#gauge).
pub struct Gauge {
    value: AtomicI64,
}

impl Gauge {
    #[inline(always)]
    const fn new() -> Self {
        Self {
            value: AtomicI64::new(0),
        }
    }

    #[inline(always)]
    pub fn get(&self) -> i64 {
        self.value.load(Ordering::Relaxed)
    }

    #[inline(always)]
    pub fn set(&self, value: i64) {
        self.value.store(value, Ordering::Relaxed);
    }

    #[inline(always)]
    pub fn add(&self, value: i64) {
        self.value.fetch_add(value, Ordering::Relaxed);
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub fn inc(&self) {
        self.add(1)
    }

    #[inline(always)]
    pub fn sub(&self, value: i64) {
        self.value.fetch_sub(value, Ordering::Relaxed);
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub fn dec(&self) {
        self.sub(1);
    }
}

// TODO: Histogram

// TODO: Summary

#[derive(PartialEq, Eq)]
struct MetricLabel {
    name: Box<str>,
    value: Box<str>,
}

impl fmt::Display for MetricLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)?;
        f.write_str("=\"")?;
        f.write_str(&self.value)?;
        f.write_char('"')
    }
}

struct NamedLabels<'a> {
    name: &'a str,
    labels: &'a [MetricLabel],
}

impl<'a> NamedLabels<'a> {
    fn new(name: &'a str, labels: &'a [MetricLabel]) -> Self {
        Self { name, labels }
    }
}

impl fmt::Display for NamedLabels<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name)?;
        if self.labels.is_empty() {
            return Ok(());
        }
        let mut first = true;
        f.write_char('{')?;
        for label in self.labels.iter() {
            if first {
                first = false;
            } else {
                f.write_char(',')?;
            }
            label.fmt(f)?;
        }
        f.write_char('}')?;
        Ok(())
    }
}

pub struct MetricInfo {
    name: Box<str>,
    help: Option<Box<str>>,
    labels: Vec<MetricLabel>,
}

impl MetricInfo {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into().into_boxed_str(),
            help: None,
            labels: Vec::new(),
        }
    }

    pub fn help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into().into_boxed_str());
        self
    }

    pub fn label(mut self, name: impl Into<String>, value: impl Into<String>) -> Self {
        self.labels.push(MetricLabel {
            name: name.into().into_boxed_str(),
            value: value.into().into_boxed_str(),
        });
        self
    }
}

pub enum MetricValue {
    Counter(&'static Counter),
    Gauge(&'static Gauge),
}

impl MetricValue {
    fn ty(&self) -> &'static str {
        match self {
            MetricValue::Counter(..) => "counter",
            MetricValue::Gauge(..) => "gauge",
        }
    }

    fn format(&self, named_labels: NamedLabels, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MetricValue::Counter(value) => {
                writeln!(f, "{named_labels} {}", value.get())?;
            }
            MetricValue::Gauge(value) => {
                writeln!(f, "{named_labels} {}", value.get())?;
            }
        }
        Ok(())
    }
}

mod private {
    use super::MetricValue;

    pub trait Sealed: Sized {
        fn create() -> Self;
        fn wrap(&'static self) -> MetricValue;
    }
}

use self::private::Sealed;

pub trait CreateMetricValue: Sealed {}

macro_rules! impl_create_metric_value {
    ($name:ident) => {
        impl Sealed for $name {
            fn create() -> Self {
                Self::new()
            }

            fn wrap(&'static self) -> MetricValue {
                MetricValue::$name(self)
            }
        }

        impl CreateMetricValue for $name {}
    };
}

impl_create_metric_value!(Counter);
impl_create_metric_value!(Gauge);

union Data<T, F> {
    value: ManuallyDrop<T>,
    f: ManuallyDrop<F>,
}

/// A metric with a lazy initialization.
///
/// # Examples
///
/// ```
/// use crate::metrics::LazyCounter;
///
/// static REQUESTS_LIST_TOTAL: LazyCounter = LazyCounter::new(|| {
///     MetricInfo::new("requests_total")
///         .help("Counter of requests.")
///         .label("query", "list")
/// });
///
/// REQUESTS_LIST_TOTAL.get().inc();
///
/// assert_eq!(REQUESTS_LIST_TOTAL.get().get(), 1);
/// ```
pub struct LazyMetric<T, F = fn() -> MetricInfo> {
    once: Once,
    data: UnsafeCell<Data<T, F>>,
}

unsafe impl<T: Sync + Send, F: Send> Sync for LazyMetric<T, F> {}

impl<T, F: FnOnce() -> MetricInfo> LazyMetric<T, F> {
    pub const fn new(f: F) -> Self {
        Self {
            once: Once::new(),
            data: UnsafeCell::new(Data {
                f: ManuallyDrop::new(f),
            }),
        }
    }

    pub fn get(&'static self) -> &'static T
    where
        T: CreateMetricValue,
    {
        self.once.call_once(|| {
            // SAFETY: `call_once` execute this closure only once.
            let data = unsafe { &mut *self.data.get() };
            let f = unsafe { ManuallyDrop::take(&mut data.f) };
            data.value = ManuallyDrop::new(T::create());
            Registry::get().register(f(), unsafe { &*data.value }.wrap());
        });

        // SAFETY: `value` initialized by closure above.
        unsafe { &(*self.data.get()).value }
    }
}

pub type LazyCounter = LazyMetric<Counter>;
pub type LazyGauge = LazyMetric<Gauge>;

struct MetricEntry {
    name: Box<str>,
    help: Option<Box<str>>,
    values: Vec<(Box<[MetricLabel]>, MetricValue)>,
}

impl MetricEntry {
    fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into().into_boxed_str(),
            help: None,
            values: Vec::new(),
        }
    }

    fn help(&mut self, help: impl Into<String>) {
        self.help = Some(help.into().into_boxed_str());
    }

    fn insert(
        &mut self,
        labels: impl Into<Vec<MetricLabel>>,
        value: MetricValue,
    ) -> Result<(), Box<[MetricLabel]>> {
        let labels = labels.into().into_boxed_slice();
        if self.values.iter().any(|(i, _)| *i == labels) {
            return Err(labels);
        }
        self.values.push((labels, value));
        Ok(())
    }
}

impl fmt::Display for MetricEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = self.name.as_ref();
        let help = self.help.as_deref().unwrap_or("Help is not specified");
        writeln!(f, "# HELP {name} {help}")?;
        writeln!(f, "# TYPE {name} {}", self.values[0].1.ty())?;
        for (labels, value) in &self.values {
            let named_labels = NamedLabels::new(name, labels);
            value.format(named_labels, f)?;
        }
        Ok(())
    }
}

static REGISTRY: OnceLock<Registry> = OnceLock::new();

pub struct Registry {
    metrics: RwLock<Vec<MetricEntry>>,
}

impl Registry {
    fn new() -> Self {
        Self {
            metrics: RwLock::new(Vec::new()),
        }
    }

    pub fn get() -> &'static Self {
        REGISTRY.get_or_init(Self::new)
    }

    fn register(&self, info: MetricInfo, value: MetricValue) {
        let named_labels = NamedLabels::new(&info.name, &info.labels);
        let ty = value.ty();
        debug!("metric: register {ty} {named_labels}");
        let labels = info.labels.into_boxed_slice();
        let mut metrics = self.metrics.write().unwrap();
        if let Some(metric) = metrics.iter_mut().find(|i| i.name == info.name) {
            if let Err(labels) = metric.insert(labels, value) {
                let named_labels = NamedLabels::new(&info.name, &labels);
                error!("metric: duplicated {ty} {named_labels}");
            }
        } else {
            let mut metric = MetricEntry::new(info.name);
            if let Some(help) = info.help {
                metric.help(help);
            }
            metric.insert(labels, value).ok();
            metrics.push(metric);
        }
    }

    #[allow(dead_code)]
    pub fn register_counter(&self, info: MetricInfo) -> &'static Counter {
        let value = Box::leak(Box::new(Counter::new()));
        self.register(info, MetricValue::Counter(value));
        value
    }

    #[allow(dead_code)]
    pub fn register_gauge(&self, info: MetricInfo) -> &'static Gauge {
        let value = Box::leak(Box::new(Gauge::new()));
        self.register(info, MetricValue::Gauge(value));
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn format_counter() {
        static COUNTER: Counter = Counter::new();
        let mut metric = MetricEntry::new("test_counter");
        metric.help("Test counter help message");
        metric.insert([], MetricValue::Counter(&COUNTER)).ok();
        assert_eq!(
            metric.to_string(),
            concat!(
                "# HELP test_counter Test counter help message\n",
                "# TYPE test_counter counter\n",
                "test_counter 0\n",
            )
        );
        COUNTER.add(3);
        assert_eq!(
            metric.to_string(),
            concat!(
                "# HELP test_counter Test counter help message\n",
                "# TYPE test_counter counter\n",
                "test_counter 3\n",
            )
        );
    }

    #[test]
    fn format_gauge() {
        static GAUGE: Gauge = Gauge::new();
        let mut metric = MetricEntry::new("test_gauge");
        metric.help("Test gauge help message");
        metric.insert([], MetricValue::Gauge(&GAUGE)).ok();
        assert_eq!(
            metric.to_string(),
            concat!(
                "# HELP test_gauge Test gauge help message\n",
                "# TYPE test_gauge gauge\n",
                "test_gauge 0\n",
            )
        );
        GAUGE.add(10);
        assert_eq!(
            metric.to_string(),
            concat!(
                "# HELP test_gauge Test gauge help message\n",
                "# TYPE test_gauge gauge\n",
                "test_gauge 10\n",
            )
        );
        GAUGE.dec();
        assert_eq!(
            metric.to_string(),
            concat!(
                "# HELP test_gauge Test gauge help message\n",
                "# TYPE test_gauge gauge\n",
                "test_gauge 9\n",
            )
        );
    }
}
