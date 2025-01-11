# Commands

- [Typable commands](#typable-commands)
  - [Command mode syntax](#command-mode-syntax)
    - [Quoting](#quoting)
    - [Expansions](#expansions)
    - [Flags](#flags)
  - [Built-ins](#built-ins)
- [Static commands](#static-commands)

## Typable commands

Typable commands are used from command mode and may take arguments. Command mode can be activated by pressing `:`.

### Command mode syntax

Command mode has a special syntax to handle arguments. This syntax is used by most commands. Note that the following commands do not use the normal command mode syntax and instead parse their arguments with custom rules. For example the shell commands below (`:insert-output`, `:append-output`, `:pipe`, `:pipe-to`, and `:run-shell-command`) pass their arguments to the configured shell program as-is.

* `:earlier`
* `:later`
* `:lsp-workspace-command`
* `:debug-start`
* `:debug-remote`
* `:debug-eval`
* `:insert-output`
* `:append-output`
* `:pipe`
* `:pipe-to`
* `:run-shell-command`

#### Quoting

By default command arguments are split on tabs and space characters. For most commands you can surround arguments in single quotes (`'`) or backticks (`` ` ``) to provide a literal value. For example the command `:open 'a b.txt'` will open a file that contains a space: `a b.txt`.

On Unix systems the backslash character may be used to escape certain characters when writing arguments without quotes. Within an argument the backslash can be used to escape either a space or tab character. For example `:open a\ b.txt` is equivalent to `:open 'a b.txt'`. The backslash can also be used to escape quote characters (`'`, `` ` ``, `"`) or the percent token (`%`) when used at the beginning of an argument. This can be used to escape a quote or expansion. For example `:echo \%sh{foo}` prints `%sh{foo}` to the statusline instead of invoking a `foo` shell command. The backslash character is treated literally in any other situation on Unix systems and always on Windows systems. For example `:echo \n` will print `\n` literally to the statusline.

Within a string, the string's quote character (`'`, `` ` `` or `"`) can be supplied twice to escape the value. For example `:echo 'hello '' world'` prints `hello ' world` to the statusline.

Double quotes behave similarly to single quotes and backticks: you can use them to surround arguments which contain spaces. Double quoted content also supports expansion of the quoted text, discussed in the expansions section below. Note that to avoid expansions within double quotes you may pass two percent characters to escape the expansion. For example `echo "%%sh{foo}"` prints `%sh{foo}` to the statusline.

#### Expansions

Most commands support _expansions_: patterns Helix recognizes and replaces. Helix recognizes anything starting with a percent token (`%`) as an expansion, for example `%sh{echo 'hello world!'}`.

Expansions take the form `%[<kind>]<open><contents><close>`. In `%sh{echo hi}`, for example, the kind is `sh` - the shell expansion - and the contents are "echo hi", with `{` and `}` acting as opening and closing delimiters. The following open/close characters are recognized as expansion delimiter pairs: `(`/`)`, `[`/`]`, `{`/`}` and `<`/`>`. Any grapheme cluster can be used as both open and close delimiters instead however: `%{cursor_line}` is equivalent to `%|cursor_line|`, `%"cursor_line"` and even `%🏴‍☠️cursor_line🏴‍☠️`.

When no kind is provided, Helix will expand a **variable**. For example `%{cursor_line}` can be used as an argument to provide the currently focused document's primary selection's cursor line as an argument. `:echo %{cursor_line}` for instance may print `1` to the statusline.

The following variables are supported:

| Name | Description |
|---   |---          |
| `cursor_line` | The one-indexed line number of the primary cursor in the currently focused document. |
| `cursor_column` | the one-indexed column number of the primary cursor in the currently focused document. This is counted as the number of grapheme clusters from the start of the line rather than bytes or codepoints. |
| `buffer_name` | The relative path of the currently focused document. `"[scratch]"` is expanded instead for scratch buffers. |
| `line_ending` | A string containing the line ending of the currently focused document. For example on Unix systems this is usually a line-feed character (`\n`) but on Windows systems this may be a carriage-return plus a line-feed (`\r\n`). The line ending kind of the currently focused document can be inspected with the `:line-ending` command. |

Aside from editor variables, the following expansions may be used:

* Unicode `%u{..}`. The contents may contain up to six hexadecimal digits corresponding to a Unicode codepoint value. For example `:echo %u{25CF}` prints `●` to the statusline.
* Shell `%sh{..}`. The contents are passed to the configured shell command. For example `:echo %sh{echo "20 * 5" | bc}` may print `100` on the statusline on Unix systems with the `bc` calculator installed.

As mentioned above, double quotes can be used to surround arguments with spaces but also support expansions within the quoted content unlike singe quotes or backticks. For example `:echo "circle: %u{25CF}"` prints `circle: ●` to the statusline.

Note that expansions are only evaluated once the Enter key is pressed in command mode.

#### Flags

Command flags are optional switches that can be used to alter the behavior of a command. For example the `:sort` command accepts an optional `--reverse` (or `-r` for short) flag which, if present, causes the sort command to reverse the sorting direction. Typing `-` will cause completions to pop up for the current command's flags.

Similar to Bash built-ins, the `"--"` flag species the end of flags. All arguments specified after `--` are treated as positional argumenst. For example you can use `:open -- -a.txt` to open a file called `"-a.txt"`.

Currently only boolean flags like `--reverse` are supported but in the future flags might accept arguments.

### Built-ins

The built-in typable commands are:

{{#include ./generated/typable-cmd.md}}

## Static Commands

Static commands take no arguments and can be bound to keys. Static commands can also be executed from the command picker (`<space>?`). The built-in static commands are:

{{#include ./generated/static-cmd.md}}
