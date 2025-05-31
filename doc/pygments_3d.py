from pygments.lexer import RegexLexer, words
from pygments.token import *

keywords_3d = (
  "where",
  "requires",
  "sizeof",
  "enum",
  "typedef",
  "struct",
  "casetype",
  "switch",
  "case",
  "default",
  "this",
  "entrypoint",
  "aligned",
  "if",
  "else",
  "mutable",
  "field_pos_64",
  "field_pos_32",
  "field_pos",
  "field_ptr",
  "field_ptr_after",
  "var",
  "abort",
  "return",
  "refining",
  "as",
  "module",
  "export",
  "output",
  "union",
  "extern",
  "probe",
  "pointer",
  "specialize",
  "align",
  "PURE"
)

# very rough lexer; not 100% precise
class CustomLexer(RegexLexer):
    name = '3D'
    aliases = ['3d']
    filenames = ['*.3d']
    tokens = {
        'root': [
            (r' ', Text),
            (r'\n', Text),
            (r'\r', Text),
            (r'//.*\n', Comment),
            (r'\/[*]([^*]|[*]+[^)])*[*]+\/', Comment),
            (words(keywords_3d, suffix=r'\b'), Keyword),
            (r'[a-zA-Z_0-9]+', Text),
            (r'.', Text),
        ]
    }