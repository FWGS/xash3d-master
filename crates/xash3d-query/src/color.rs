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
        // TODO: unicode width
        let mut width = 0;

        #[cfg_attr(not(feature = "color"), allow(unused_mut))]
        let mut iter = xash3d_colored::str::split(self.text);

        #[cfg(feature = "color")]
        if self.enable {
            use crossterm::style::Stylize;
            use xash3d_colored::Color;

            for (color, text) in iter.by_ref() {
                width += text.chars().count();
                let colored = match color {
                    Color::Black => text.black(),
                    Color::Red => text.red(),
                    Color::Green => text.green(),
                    Color::Yellow => text.yellow(),
                    Color::Blue => text.blue(),
                    Color::Cyan => text.cyan(),
                    Color::Magenta => text.magenta(),
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
