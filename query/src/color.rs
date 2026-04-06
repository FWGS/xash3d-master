use std::fmt;

#[cfg(feature = "color")]
use std::io;

pub struct Colored<'a> {
    inner: &'a str,
    forced: bool,
}

impl<'a> Colored<'a> {
    pub fn new(s: &'a str, forced: bool) -> Self {
        Self { inner: s, forced }
    }
}

impl fmt::Display for Colored<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        #[cfg(feature = "color")]
        use crossterm::{style::Stylize, tty::IsTty};

        // TODO: unicode width
        let mut width = 0;

        #[cfg(feature = "color")]
        if self.forced || io::stdout().is_tty() {
            use xash3d_protocol::color;

            for (color, text) in color::ColorIter::new(self.inner) {
                width += text.chars().count();
                let colored = match color::Color::try_from(color) {
                    Ok(color::Color::Black) => text.black(),
                    Ok(color::Color::Red) => text.red(),
                    Ok(color::Color::Green) => text.green(),
                    Ok(color::Color::Yellow) => text.yellow(),
                    Ok(color::Color::Blue) => text.blue(),
                    Ok(color::Color::Cyan) => text.cyan(),
                    Ok(color::Color::Magenta) => text.magenta(),
                    Ok(color::Color::White) => text.white(),
                    _ => text.reset(),
                };
                colored.fmt(fmt)?;
            }
        }

        #[cfg(not(feature = "color"))]
        for (_, text) in color::ColorIter::new(self.inner) {
            width += text.chars().count();
            text.fmt(fmt)?;
        }

        if let Some(w) = fmt.width() {
            let c = fmt.fill();
            for _ in width..w {
                write!(fmt, "{c}")?;
            }
        }

        Ok(())
    }
}
