use std::borrow::Cow;

use helix_core::command_line::{ArgsParser, ParseMode, Token, TokenKind};

use anyhow::{anyhow, bail, Result};

use crate::Editor;

/// Variables that can be expanded in the command mode (`:`) via the expansion syntax.
///
/// Variable expansion on the command line takes the form `%{variable_name}`. Unlike Unicode
/// (`%u{hex}`) or shell (`%sh{..}`) expansions, variable expansions take no "expander" name.
///
/// To add a new variable follow these steps:
///
/// * Add the new enum member to `Variable` below.
/// * Add a branch in `Variable::as_str`, converting the name from TitleCase to snake_case.
/// * Add a branch in `Variable::from_name` with the reverse association.
/// * Add the new variable to the `VARIABLES` constant below - this enables completion.
/// * Add a branch in the `expand_variable` function to read the value from the editor.
/// * Add the new variable to the documentation in `book/src/commands.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Variable {
    /// The one-indexed line number of the primary cursor in the currently focused document.
    CursorLine,
    /// The one-indexed column number of the primary cursor in the currently focused document.
    ///
    /// Note that this is the count of grapheme clusters from the start of the line (regardless of
    /// softwrap) - the same as the `position` element in the statusline.
    CursorColumn,
    /// The display name of the currently focused document.
    ///
    /// This corresponds to `crate::Document::display_name`.
    BufferName,
    /// A string containing the line-ending of the currently focused document.
    LineEnding,
}

impl Variable {
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::CursorLine => "cursor_line",
            Self::CursorColumn => "cursor_column",
            Self::BufferName => "buffer_name",
            Self::LineEnding => "line_ending",
        }
    }

    pub fn from_name(s: &str) -> Option<Self> {
        match s {
            "cursor_line" => Some(Self::CursorLine),
            "cursor_column" => Some(Self::CursorColumn),
            "buffer_name" => Some(Self::BufferName),
            "line_ending" => Some(Self::LineEnding),
            _ => None,
        }
    }
}

/// The set of recognized variable names.
pub const VARIABLES: &[&str] = &[
    Variable::CursorLine.as_str(),
    Variable::CursorColumn.as_str(),
    Variable::BufferName.as_str(),
    Variable::LineEnding.as_str(),
];

/// Expands the given command line token.
///
/// Note that the lifetime of the expanded variable is only bound to the input token and not the
/// `Editor`. See `expand_variable` below for more discussion of lifetimes.
pub fn expand<'a>(editor: &Editor, token: Token<'a>) -> Result<Cow<'a, str>> {
    // Note: see the `TokenKind` documentation for more details on how each branch should expand.
    match token.kind {
        TokenKind::Raw | TokenKind::Quoted => Ok(token.content),
        TokenKind::VariableExpansion => {
            let var = Variable::from_name(&token.content)
                .ok_or_else(|| anyhow!("unknown variable '{}'", token.content))?;

            expand_variable(editor, var)
        }
        TokenKind::UnicodeExpansion => {
            if let Some(ch) = u32::from_str_radix(token.content.as_ref(), 16)
                .ok()
                .and_then(char::from_u32)
            {
                Ok(Cow::Owned(ch.to_string()))
            } else {
                Err(anyhow!(
                    "could not interpret '{}' as a Unicode character code",
                    token.content
                ))
            }
        }
        TokenKind::Expand => {
            let mut escaped = String::new();
            let mut start = 0;

            while let Some(offset) = token.content[start..].find('%') {
                let idx = start + offset;
                if token.content.as_bytes().get(idx + '%'.len_utf8()).copied() == Some(b'%') {
                    // Treat two percents in a row as an escaped percent.
                    escaped.push_str(&token.content[start..=idx]);
                    // Skip over the second percent.
                    start = idx + ('%'.len_utf8() * 2);
                } else {
                    // Otherwise interpret the percent as an expansion. Push up to (but not
                    // including) the percent token.
                    escaped.push_str(&token.content[start..idx]);
                    // Then parse the expansion,
                    let mut parser =
                        ArgsParser::new(&token.content[idx..], ParseMode::Parameters, true);
                    let percent_token = parser
                        .parse_percent_token()
                        .unwrap()
                        .map_err(|err| anyhow!("{err}"))?;
                    // expand it (this is recursive),
                    escaped.push_str(expand(editor, percent_token)?.as_ref());
                    // and move forward to the end of the expansion.
                    start = idx + parser.pos();
                }
            }

            if escaped.is_empty() {
                Ok(token.content)
            } else {
                escaped.push_str(&token.content[start..]);
                Ok(Cow::Owned(escaped))
            }
        }
        TokenKind::ShellExpansion => {
            use std::process::{Command, Stdio};

            // TODO: there is no protection here against a shell command taking a long time.
            // Ideally you should be able to hit `<ret>` in command mode and then be able to
            // cancel the invocation (for example with `<C-c>`) if it takes longer than you'd
            // like.

            let config = editor.config();
            let shell = &config.shell;
            let mut process = Command::new(&shell[0]);
            process
                .args(&shell[1..])
                .arg(token.content.as_ref())
                .stdin(Stdio::null())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped());

            let output = match process.spawn() {
                Ok(process) => process.wait_with_output()?,
                Err(err) => {
                    bail!("Failed to start shell: {err}");
                }
            };

            let text = if !output.status.success() {
                if output.stderr.is_empty() {
                    match output.status.code() {
                        Some(exit_code) => bail!("Shell command failed with status {exit_code}"),
                        None => bail!("Shell command failed"),
                    }
                }
                String::from_utf8_lossy(&output.stderr)
            } else if !output.stderr.is_empty() {
                // stderr is prioritized over stdout
                let stderr = String::from_utf8_lossy(&output.stderr);
                log::debug!("Command printed to stderr: {stderr}");
                stderr
            } else {
                String::from_utf8_lossy(&output.stdout)
            };

            // Trim exactly one trailing newline if it exists.
            let mut text = text.into_owned();
            if text.ends_with('\n') {
                text.pop();
            }

            Ok(Cow::Owned(text))
        }
    }
}

// Note: the lifetime of the expanded variable (the `Cow`) must not be tied to the lifetime of
// the borrow of `Editor`. That would prevent commands from mutating the `Editor` until the
// command consumed or cloned all arguments - this is poor ergonomics. A sensible thing for this
// function to return then, instead, would normally be a `String`. We can return some statically
// known strings like the scratch buffer name or line ending strings though, so this function
// returns a `Cow<'static, str>` instead.
fn expand_variable(editor: &Editor, variable: Variable) -> Result<Cow<'static, str>> {
    match variable {
        Variable::CursorLine => {
            let (view, doc) = current_ref!(editor);
            let text = doc.text().slice(..);
            let cursor_line = doc.selection(view.id).primary().cursor_line(text);
            Ok(Cow::Owned((cursor_line + 1).to_string()))
        }
        Variable::CursorColumn => {
            let (view, doc) = current_ref!(editor);
            let text = doc.text().slice(..);
            let cursor = doc.selection(view.id).primary().cursor(text);
            let position = helix_core::coords_at_pos(text, cursor);
            Ok(Cow::Owned((position.col + 1).to_string()))
        }
        Variable::BufferName => {
            // Note: usually we would use `Document::display_name` but we can statically borrow
            // the scratch buffer name by partially reimplementing `display_name`.
            let doc = doc!(editor);
            if let Some(path) = doc.relative_path() {
                Ok(Cow::Owned(path.to_string_lossy().into_owned()))
            } else {
                Ok(Cow::Borrowed(crate::document::SCRATCH_BUFFER_NAME))
            }
        }
        Variable::LineEnding => Ok(Cow::Borrowed(doc!(editor).line_ending.as_str())),
    }
}
