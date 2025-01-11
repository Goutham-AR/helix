use std::{borrow::Cow, collections::HashMap, fmt, ops, vec};

use unicode_segmentation::UnicodeSegmentation;

/// Splits a command line into the command and arguments parts.
///
/// The third enum member describes whether the command part is finished. When this boolean is
/// true the completion code for the command line should complete command names, otherwise
/// command arguments.
pub fn split(line: &str) -> (&str, &str, bool) {
    const SEPARATOR_PATTERN: [char; 2] = [' ', '\t'];

    let (command, rest) = line.split_once(SEPARATOR_PATTERN).unwrap_or((line, ""));

    let complete_command =
        command.is_empty() || (rest.trim().is_empty() && !line.ends_with(SEPARATOR_PATTERN));

    (command, rest, complete_command)
}

/// A Unix-like flag that a command may accept.
///
/// For example the `:sort` command accepts a `--reverse` (or `-r` for shorthand) boolean flag
/// which controls the direction of sorting. In the future flags could also support accepting
/// arguments themselves.
#[derive(Debug, Clone, Copy)]
pub struct Flag {
    /// The name of the flag.
    ///
    /// This value is also used to construct the "longhand" version of the flag. For example a
    /// flag with a name "reverse" has a longhand `--reverse`.
    ///
    /// This value should be supplied when reading a flag out of the [Args] with [Args::get_flag]
    /// and [Args::has_flag]. The `:sort` command implementation for example should ask for
    /// `args.has_flag("reverse")`.
    pub name: &'static str,
    /// The character that can be used as a shorthand for the flag, optionally.
    ///
    /// For example a flag like "reverse" mentioned above might take an alias `Some('r')` to
    /// allow specifying the flag as `-r`.
    pub alias: Option<char>,
    pub doc: &'static str,
    /// The completion function to use when specifying an argument for a flag.
    ///
    /// This is currently unused and should always be set to `None`.
    // TODO: when commands start taking arguments in their flags, add completer functions.
    pub completer: Option<()>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseMode {
    /// Interpret nothing: the entire command line is treated as one parameter.
    ///
    /// This mode is used for shell commands like `:run-shell-command` which should pass their
    /// input to the shell command as-is.
    Raw,
    /// Split the input into separate parameters on whitespace while respecting quoting and
    /// expansions.
    ///
    /// This mode splits arguments so that an input like "hello world" becomes two arguments:
    /// `["hello", "world"]`.
    Parameters,
}

#[derive(Debug, Clone, Copy)]
pub struct Signature {
    /// The minimum and optionally maximum number of positional arguments a command may take.
    ///
    /// For example accepting exactly one positional can be specified with `(1, Some(1))` while
    /// accepting zero-or-more positionals can be specified as `(0, None)`.
    pub positionals: (usize, Option<usize>),
    /// The strategy to use while parsing the command line.
    ///
    /// Most commands should use `ParseMode::Parameters`. `ParseMode::Raw` is meant for commands
    /// like `:run-shell-command` that should accept the entire input as-is.
    pub parse_mode: ParseMode,
    /// A set of flags that a command may accept.
    ///
    /// See the `Flag` struct for more info.
    pub flags: &'static [Flag],
}

// This constant allows defining signatures with the `..` shorthand, similar to
// `..Default::default()` but this can be used within constants. The `positionals` field should
// always be overwritten.
pub const DEFAULT_SIGNATURE: Signature = Signature {
    positionals: (0, None),
    parse_mode: ParseMode::Parameters,
    flags: &[],
};

impl Signature {
    fn check_positional_count(&self, actual: usize) -> Result<(), ParseArgsError<'static>> {
        let (min, max) = self.positionals;
        if min <= actual && max.unwrap_or(usize::MAX) >= actual {
            Ok(())
        } else {
            Err(ParseArgsError::WrongPositionalCount { min, max, actual })
        }
    }
}

#[derive(Debug, Clone)]
pub enum ParseArgsError<'a> {
    WrongPositionalCount {
        min: usize,
        max: Option<usize>,
        actual: usize,
    },
    UnterminatedToken {
        token: Token<'a>,
    },
    DuplicatedFlag {
        flag: &'static str,
    },
    UnknownFlag {
        text: Cow<'a, str>,
    },
    FlagMissingArgument {
        flag: &'static str,
    },
    MissingExpansionDelimiter {
        expansion: &'a str,
    },
    UnknownExpansion {
        kind: &'a str,
    },
}

impl fmt::Display for ParseArgsError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongPositionalCount { min, max, actual } => {
                f.write_str("expected ")?;
                match (min, max) {
                    (0, Some(0)) => f.write_str("no arguments")?,
                    (min, Some(max)) if min == max => {
                        f.write_fmt(format_args!("exactly {min} arguments"))?
                    }
                    (min, _) if actual < min => {
                        f.write_fmt(format_args!("at least {min} arguments"))?
                    }
                    (_, Some(max)) if actual > max => {
                        f.write_fmt(format_args!("at most {max} arguments"))?
                    }
                    _ => unreachable!(),
                }

                f.write_fmt(format_args!(", got {actual}"))
            }
            Self::UnterminatedToken { token } => {
                f.write_fmt(format_args!("unterminated token {}", token.content))
            }
            Self::DuplicatedFlag { flag } => {
                f.write_fmt(format_args!("flag '--{flag}' specified more than once"))
            }
            Self::UnknownFlag { text } => f.write_fmt(format_args!("unknown flag '{text}'")),
            Self::FlagMissingArgument { flag } => {
                f.write_fmt(format_args!("flag '--{flag}' missing an argument"))
            }
            Self::MissingExpansionDelimiter { expansion } => f.write_fmt(format_args!(
                "missing a string delimiter after '%{expansion}'"
            )),
            Self::UnknownExpansion { kind } => {
                f.write_fmt(format_args!("unknown expansion '{kind}'"))
            }
        }
    }
}

impl std::error::Error for ParseArgsError<'_> {}

/// The type of argument being written.
///
/// The token kind decides how an argument in the command line will be expanded upon hitting
/// `<ret>` in command mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    /// Unquoted text.
    ///
    /// For example in `:echo hello world`, "hello" and "world" are raw tokens.
    Raw,
    /// Quoted text which is interpreted literally.
    ///
    /// The purpose of this kind is to avoid splitting arguments on whitespace. For example
    /// `:open 'a b.txt'` will result in opening a file with a single argument `"a b.txt"`.
    ///
    /// Using expansions within single quotes or backticks will result in the expansion text
    /// being shown literally. For example `:echo '%u{0020}` will print `"%u{0020}"` to the
    /// statusline.
    Quoted,
    /// Text within double quote delimiters (`"`).
    ///
    /// The inner text of a double quoted argument can be further expanded. For example
    /// `:echo "line: #%{cursor_line}"` could print `"line: #1"` to the statusline.
    Expand,
    /// Expansion for editor variables.
    ///
    /// See `helix-view/src/expansion.rs` and the `Variable` enum for more details.
    VariableExpansion,
    /// Expansion of Unicode codepoints by their hexadecimal value.
    ///
    /// For example `%u{0020}` can be used to represent an ASCII space.
    UnicodeExpansion,
    /// Shell expansions.
    ///
    /// The inner text of the expansion is executed as a command with no stdin.
    ShellExpansion,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub start_byte: usize,
    pub content: Cow<'a, str>,
    pub is_terminated: bool,
}

impl Token<'_> {
    pub fn empty_at(start_byte: usize) -> Self {
        Self {
            kind: TokenKind::Raw,
            start_byte,
            content: Cow::Borrowed(""),
            is_terminated: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ArgsParser<'a> {
    input: &'a str,
    parse_mode: ParseMode,
    /// Whether to return errors in the iterator for failed validations like unterminated strings
    /// or expansions. When this is set to `false` the iterator will never return `Err`.
    validate: bool,
    /// The current byte index of the input being considered.
    pos: usize,
}

impl<'a> ArgsParser<'a> {
    pub fn new(input: &'a str, parse_mode: ParseMode, validate: bool) -> Self {
        Self {
            input,
            parse_mode,
            validate,
            pos: 0,
        }
    }

    /// Returns the current byte index position of the parser in the input.
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// Whether the parser is at the end of the line.
    fn eol(&self) -> bool {
        self.pos == self.input.len()
    }

    fn byte(&self) -> u8 {
        self.input.as_bytes()[self.pos]
    }

    fn peek_byte(&self) -> Option<u8> {
        self.input.as_bytes().get(self.pos + 1).copied()
    }

    fn prev_byte(&self) -> Option<u8> {
        self.pos
            .checked_sub(1)
            .map(|idx| self.input.as_bytes()[idx])
    }

    fn skip_blanks(&mut self) {
        while !self.eol() {
            match self.byte() {
                b' ' | b'\t' => self.pos += 1,
                _ => break,
            }
        }
    }

    fn parse_unquoted(&mut self) -> Cow<'a, str> {
        // Note that `String::new` starts with no allocation. We only allocate if we see a
        // backslash escape (on Unix only).
        let mut escaped = String::new();
        let mut start = self.pos;

        while !self.eol() {
            if matches!(self.byte(), b' ' | b'\t') {
                if cfg!(unix) && self.prev_byte() == Some(b'\\') {
                    // Push everything up to but not including the backslash and then this
                    // whitespace character.
                    escaped.push_str(&self.input[start..self.pos - 1]);
                    escaped.push(self.byte() as char);
                    start = self.pos + 1;
                } else if escaped.is_empty() {
                    return Cow::Borrowed(&self.input[start..self.pos]);
                } else {
                    break;
                }
            }

            self.pos += 1;
        }

        // Special case for a trailing backslash on Unix: exclude the backslash from the content.
        // This improves the behavior of completions like `":open a\\"` (trailing backslash).
        let end = if cfg!(unix) && self.prev_byte() == Some(b'\\') {
            self.pos - 1
        } else {
            self.pos
        };

        if escaped.is_empty() {
            assert_eq!(self.pos, self.input.len());
            Cow::Borrowed(&self.input[start..end])
        } else {
            escaped.push_str(&self.input[start..end]);
            Cow::Owned(escaped)
        }
    }

    /// Parses a string quoted by the given grapheme cluster.
    ///
    /// The position of the parser is asserted to be immediately after the quote grapheme cluster.
    fn parse_quoted(&mut self, quote: &str) -> (Cow<'a, str>, bool) {
        assert!(self.input[..self.pos].ends_with(quote));

        let mut escaped = String::new();

        while let Some(offset) = self.input[self.pos..].find(quote) {
            let idx = self.pos + offset;

            if self.input[idx + quote.len()..].starts_with(quote) {
                // Treat two quotes in a row as an escape.
                escaped.push_str(&self.input[self.pos..idx + quote.len()]);
                self.pos += quote.len();
            } else {
                // Otherwise this quote string is finished.
                let quoted = if escaped.is_empty() {
                    Cow::Borrowed(&self.input[self.pos..idx])
                } else {
                    escaped.push_str(&self.input[self.pos..idx]);
                    Cow::Owned(escaped)
                };
                // Advance past the closing quote.
                self.pos = idx + quote.len();
                return (quoted, true);
            }

            // Advance past the quote.
            self.pos += offset + quote.len();
        }

        let quoted = if escaped.is_empty() {
            Cow::Borrowed(&self.input[self.pos..])
        } else {
            escaped.push_str(&self.input[self.pos..]);
            Cow::Owned(escaped)
        };
        self.pos = self.input.len();

        (quoted, false)
    }

    /// Parses the percent token expansion under the parser's cursor.
    ///
    /// This function should only be called when the parser's cursor is on a non-escaped percent
    /// token.
    pub fn parse_percent_token(&mut self) -> Option<Result<Token<'a>, ParseArgsError<'a>>> {
        assert_eq!(self.byte(), b'%');

        self.pos += 1;
        let type_start = self.pos;
        while !self.eol() && self.byte().is_ascii_lowercase() {
            self.pos += 1;
        }
        let kind_name = &self.input[type_start..self.pos];

        let next_grapheme = self.input[self.pos..]
            .graphemes(true)
            .next()
            .inspect(|grapheme| self.pos += grapheme.len());
        let opening_delimiter = match next_grapheme {
            Some(" " | "\t") | None => {
                return if self.validate {
                    Some(Err(ParseArgsError::MissingExpansionDelimiter {
                        expansion: kind_name,
                    }))
                } else {
                    // TODO: is this correct?
                    None
                };
            }
            Some(g) => g,
        };
        // The start byte for expansions is the start of the content - after the opening
        // delimiter grapheme.
        let start_byte = self.pos;

        let kind = match kind_name {
            "" => TokenKind::VariableExpansion,
            "u" => TokenKind::UnicodeExpansion,
            "sh" => TokenKind::ShellExpansion,
            _ if self.validate => {
                return Some(Err(ParseArgsError::UnknownExpansion { kind: kind_name }));
            }
            _ => TokenKind::Quoted,
        };

        const PAIRS: [(u8, u8); 4] = [(b'(', b')'), (b'[', b']'), (b'{', b'}'), (b'<', b'>')];

        let (content, is_terminated) = if let Some((open, close)) = PAIRS
            .iter()
            .find(|(open, _)| opening_delimiter.as_bytes() == [*open])
            .copied()
        {
            self.parse_quoted_balanced(open, close)
        } else {
            self.parse_quoted(opening_delimiter)
        };

        let token = Token {
            kind,
            start_byte,
            content,
            is_terminated,
        };

        if self.validate && !is_terminated {
            return Some(Err(ParseArgsError::UnterminatedToken { token }));
        }

        Some(Ok(token))
    }

    /// Parse the next string under the cursor given an open and closing pair.
    ///
    /// The open and closing pair are different ASCII characters. The cursor is asserted to be
    /// advanced one past the opening pair.
    ///
    /// This function parses with nesting support. `%sh{echo {hello}}` for example should consume
    /// the entire input and not quit after the first `'}'` character is found.
    fn parse_quoted_balanced(&mut self, open: u8, close: u8) -> (Cow<'a, str>, bool) {
        assert_eq!(self.prev_byte(), Some(open));
        let start = self.pos;
        let mut level = 1;

        while let Some(offset) = self.input[self.pos..].find([open as char, close as char]) {
            let idx = self.pos + offset;
            // Move past the delimiter.
            self.pos = idx + 1;

            if self.input.as_bytes()[idx] == open {
                level += 1;
            } else if self.input.as_bytes()[idx] == close {
                level -= 1;
                if level == 0 {
                    break;
                }
            } else {
                unreachable!()
            }
        }

        // If no open or close pairs were found, move to the end of the input.
        if self.pos == start {
            self.pos = self.input.len();
        }

        let is_terminated = level == 0;
        let end = if is_terminated {
            // Exclude the closing delimiter from the token's content.
            self.pos - 1
        } else {
            self.pos
        };

        (Cow::Borrowed(&self.input[start..end]), is_terminated)
    }
}

impl<'a> Iterator for ArgsParser<'a> {
    type Item = Result<Token<'a>, ParseArgsError<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.eol() {
            return None;
        }

        // In 'raw' mode, accept the entire input as one argument.
        if self.parse_mode == ParseMode::Raw {
            self.pos = self.input.len();
            return Some(Ok(Token {
                kind: TokenKind::Raw,
                start_byte: 0,
                content: Cow::Borrowed(self.input),
                is_terminated: false,
            }));
        }

        self.skip_blanks();
        if self.eol() {
            return None;
        }

        let byte = self.byte();
        match byte {
            b'"' | b'\'' | b'`' => {
                self.pos += 1;
                // The start byte for quote tokens is within the quoted content.
                let start_byte = self.pos;
                let quote_bytes = &[byte];
                // SAFETY: an ASCII byte ('"' or '\'' or '`' in this branch) is valid UTF-8.
                let quote_grapheme = unsafe { std::str::from_utf8_unchecked(quote_bytes) };
                let (content, is_terminated) = self.parse_quoted(quote_grapheme);
                let token = Token {
                    kind: match byte {
                        b'"' => TokenKind::Expand,
                        _ => TokenKind::Quoted,
                    },
                    start_byte,
                    content,
                    is_terminated,
                };

                Some(if self.validate && !is_terminated {
                    Err(ParseArgsError::UnterminatedToken { token })
                } else {
                    Ok(token)
                })
            }
            b'%' => self.parse_percent_token(),
            _ => {
                // The start byte for raw tokens is the beginning of the input.
                let start_byte = self.pos;

                // Allow backslash escaping on Unix for quotes or expansions
                if cfg!(unix)
                    && byte == b'\\'
                    && matches!(self.peek_byte(), Some(b'"' | b'\'' | b'`' | b'%'))
                {
                    self.pos += 1;
                }

                Some(Ok(Token {
                    kind: TokenKind::Raw,
                    start_byte,
                    content: self.parse_unquoted(),
                    is_terminated: false,
                }))
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum CompletionState {
    Positional,
    Flag,
    FlagArgument,
}

/// A set of arguments provided to a command on the command line.
///
/// This struct contains both positional arguments - "regular" arguments that have an index -
/// and flags. For example the `:write` command could take a flag `--no-format` which would
/// prevent LSP or external formatting. In the command line `:write --no-format foo.rs` would
/// have one boolean flag `--no-format` and one positional argument `foo.rs`.
///
/// The `Args` type can be treated essentially as a slice when accessing positional arguments.
/// `for arg in args` is valid as well as indexing into the positionals, like `&args[0]`.
/// Flags are excluded from this indexing or iterating no matter where they were specified in the
/// command line. For a command line like `:write --no-format foo.rs` for example, `&args[0]`
/// would correspond to the positional argument `foo.rs`.
///
/// Typable commands declare a signature of minimum and (optionally) maximum positional arguments
/// to accept and this is checked before invoking a command so indexing into `Args` within a
/// command's accepted range is safe.
#[derive(Debug)]
pub struct Args<'a> {
    positionals: Vec<Cow<'a, str>>,
    flags: HashMap<&'static str, Cow<'a, str>>,
    completion_state: CompletionState,
}

impl<'a> Args<'a> {
    pub fn parse(
        input: &'a str,
        signature: Signature,
        validate: bool,
    ) -> Result<Self, ParseArgsError<'a>> {
        let tokens = ArgsParser::new(input, signature.parse_mode, validate)
            .collect::<Result<Vec<_>, _>>()?;
        Self::from_tokens(
            tokens.into_iter().map(|token| token.content),
            signature,
            validate,
        )
    }

    pub fn from_tokens(
        tokens: impl IntoIterator<Item = Cow<'a, str>>,
        signature: Signature,
        validate: bool,
    ) -> Result<Self, ParseArgsError<'a>> {
        let mut tokens = tokens.into_iter();
        let mut positionals = Vec::new();
        let mut flags = HashMap::new();
        let mut state = CompletionState::Positional;
        let mut only_positionals = matches!(signature.parse_mode, ParseMode::Raw);

        while let Some(token) = tokens.next() {
            if token == "--" {
                only_positionals = true;
                state = CompletionState::Flag;
            } else if !only_positionals && token.starts_with('-') {
                state = CompletionState::Flag;
                let flag = if let Some(longhand) = token.strip_prefix("--") {
                    signature.flags.iter().find(|flag| flag.name == longhand)
                } else {
                    let shorthand = token.strip_prefix('-').unwrap();
                    signature.flags.iter().find(|flag| {
                        flag.alias.is_some_and(|ch| {
                            shorthand.starts_with(ch) && ch.len_utf8() == shorthand.len()
                        })
                    })
                };

                let flag = match flag {
                    Some(flag) => flag,
                    None if validate => return Err(ParseArgsError::UnknownFlag { text: token }),
                    None => continue,
                };

                if validate && flags.contains_key(flag.name) {
                    return Err(ParseArgsError::DuplicatedFlag { flag: flag.name });
                }

                let flag_value = if flag.completer.is_some() {
                    match tokens.next() {
                        Some(arg_token) => {
                            state = CompletionState::FlagArgument;
                            arg_token
                        }
                        // If the flag's argument isn't present and we're validating/accepting the
                        // input, error.
                        None if validate => {
                            return Err(ParseArgsError::FlagMissingArgument { flag: flag.name });
                        }
                        None => continue,
                    }
                } else {
                    Cow::Borrowed("")
                };

                flags.insert(flag.name, flag_value);
            } else {
                positionals.push(token);
                state = CompletionState::Positional;
            }
        }

        if validate {
            signature.check_positional_count(positionals.len())?;
        }

        Ok(Self {
            positionals,
            flags,
            completion_state: state,
        })
    }

    /// A constructor for blank arguments: no positionals or flags.
    pub fn empty() -> Self {
        Self {
            positionals: Default::default(),
            flags: Default::default(),
            completion_state: CompletionState::Positional,
        }
    }

    /// Returns the kind of argument the last token is considered to be.
    ///
    /// For example if the last argument in the command line is `--foo` then the argument may be
    /// considered to be a flag.
    pub fn completion_state(&self) -> CompletionState {
        self.completion_state
    }

    /// Returns the number of positionals supplied in the input.
    ///
    /// This number does not account for any flags passed in the input.
    pub fn len(&self) -> usize {
        self.positionals.len()
    }

    /// Checks whether the arguments contain no positionals.
    ///
    /// Note that this function returns `true` if there are no positional arguments even if the
    /// input contained flags.
    pub fn is_empty(&self) -> bool {
        self.positionals.is_empty()
    }

    /// Gets the first positional argument, if one exists.
    pub fn first(&'a self) -> Option<&'a str> {
        self.positionals.first().map(AsRef::as_ref)
    }

    /// Gets the positional argument at the given index, if one exists.
    pub fn get(&'a self, index: usize) -> Option<&'a str> {
        self.positionals.get(index).map(AsRef::as_ref)
    }

    /// Gets the value associated with a flag's long name if the flag was provided.
    ///
    /// This function should be preferred over [Self::has_flag] when the flag accepts an argument.
    pub fn get_flag(&'a self, name: &'static str) -> Option<&'a str> {
        self.flags.get(name).map(AsRef::as_ref)
    }

    /// Checks if a flag was provided in the arguments.
    ///
    /// This function should be preferred over [Self::get_flag] for boolean flags - flags that
    /// either are present or not.
    pub fn has_flag(&self, name: &'static str) -> bool {
        self.flags.contains_key(name)
    }
}

// `arg[0]`
impl ops::Index<usize> for Args<'_> {
    type Output = str;

    fn index(&self, index: usize) -> &Self::Output {
        self.positionals[index].as_ref()
    }
}

// `args[1..]`
impl<'a> ops::Index<ops::RangeFrom<usize>> for Args<'a> {
    type Output = [Cow<'a, str>];

    #[inline]
    fn index(&self, index: ops::RangeFrom<usize>) -> &Self::Output {
        &self.positionals[index]
    }
}

// `for arg in args`
impl<'a> IntoIterator for Args<'a> {
    type Item = Cow<'a, str>;
    type IntoIter = vec::IntoIter<Cow<'a, str>>;

    fn into_iter(self) -> Self::IntoIter {
        self.positionals.into_iter()
    }
}

/// Replaces the given completion text with a quoted version if the text contains characters
/// that would be parsed as separators or expansions.
pub fn escape_completion(text: Cow<str>) -> Cow<str> {
    if text.contains([' ', '\t', '%']) {
        Cow::Owned(format!("'{text}'"))
    } else {
        text
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[track_caller]
    fn assert_tokens(input: &str, expected: &[&str]) {
        let actual: Vec<_> = ArgsParser::new(input, ParseMode::Parameters, true)
            .map(|arg| arg.unwrap().content)
            .collect();
        let actual: Vec<_> = actual.iter().map(|c| c.as_ref()).collect();

        assert_eq!(actual.as_slice(), expected);
    }

    #[test]
    fn parse_spaces() {
        assert_tokens("", &[]);
        assert_tokens("hello", &["hello"]);
        assert_tokens("hello world", &["hello", "world"]);
        assert_tokens("hello\t \tworld", &["hello", "world"]);
    }

    #[cfg(unix)]
    #[test]
    fn parse_space_escaping() {
        assert_tokens(r#"hello\ world"#, &["hello world"]);
        assert_tokens(r#"one\ two three"#, &["one two", "three"]);
        assert_tokens(r#"one two\ three"#, &["one", "two three"]);
        // Trailing backslash is ignored.
        assert_tokens(r#"hello\"#, &["hello"]);
        // The backslash at the start of the quote makes the quote be treated as raw.
        // For the backslash before the ending quote the token is already considered raw so the
        // backslash and quote are treated literally.
        assert_tokens(
            r#"echo \"hello        world\""#,
            &["echo", r#""hello"#, r#"world\""#],
        );
    }

    #[test]
    fn parse_backslash() {
        assert_tokens(r#"\n"#, &["\\n"]);
    }

    #[test]
    fn parse_quoting() {
        // Using a quote character twice escapes it:
        assert_tokens(r#"''"#, &[""]);
        assert_tokens(r#""""#, &[""]);
        assert_tokens(r#"``"#, &[""]);
        assert_tokens(r#"echo """#, &["echo", ""]);

        assert_tokens(r#"'hello'"#, &["hello"]);
        assert_tokens(r#"'hello world'"#, &["hello world"]);

        assert_tokens(r#""hello "" world""#, &["hello \" world"]);
    }

    #[test]
    fn parse_expansions() {
        // Pair delimiters:
        assert_tokens(r#"echo %{hello world}"#, &["echo", "hello world"]);
        assert_tokens(r#"echo %[hello world]"#, &["echo", "hello world"]);
        assert_tokens(r#"echo %(hello world)"#, &["echo", "hello world"]);
        assert_tokens(r#"echo %<hello world>"#, &["echo", "hello world"]);
        // Any character can be used as a delimiter:
        assert_tokens(r#"echo %|hello world|"#, &["echo", "hello world"]);
        // Yes, even this crazy stuff. Multi-codepoint grapheme clusters are supported too.
        assert_tokens(r#"echo %🏴‍☠️hello world🏴‍☠️"#, &["echo", "hello world"]);
        // When invoking a command, double precents can be used within a string as an escape for
        // the percent. This is done in the expansion code though, not in the parser here.
        assert_tokens(r#"echo "%%hello world""#, &["echo", "%%hello world"]);
        // Different kinds of quotes nested:
        assert_tokens(
            r#"echo "%sh{echo 'hello world'}""#,
            &["echo", r#"%sh{echo 'hello world'}"#],
        );
        // Nesting of the expansion delimiter:
        assert_tokens(r#"echo %{hello {} world}"#, &["echo", "hello {} world"]);
        assert_tokens(r#"echo %{hello {{}} world}"#, &["echo", "hello {{}} world"]);
    }
}
