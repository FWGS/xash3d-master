use std::fmt;

pub struct Colored<'a> {
    text: &'a str,
    #[cfg_attr(not(feature = "color"), allow(dead_code))]
    enable: bool,
}

impl<'a> Colored<'a> {
    pub fn new(text: &'a str, enable: bool) -> Self {
        Self { text, enable }
    }
}

impl fmt::Display for Colored<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use xash3d_protocol::color;

        // TODO: unicode width
        let mut width = 0;

        #[cfg_attr(not(feature = "color"), allow(unused_mut))]
        let mut iter = color::ColorIter::new(self.text);

        #[cfg(feature = "color")]
        if self.enable {
            use crossterm::style::Stylize;

            for (color, text) in iter.by_ref() {
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

        for (_, text) in iter {
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
