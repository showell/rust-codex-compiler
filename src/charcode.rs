// Codex `char-code`, measured from the compiler by ladder charcode_probe.py.
// NOT ASCII: a frequency-ordered private alphabet, 1..96. 0 means the byte
// has no code. See that script for why this cannot be transcribed by hand.
pub const CHAR_CODE: [u8; 128] = [
    0, //   0 (not in the alphabet)
    0, //   1 (not in the alphabet)
    0, //   2 (not in the alphabet)
    0, //   3 (not in the alphabet)
    0, //   4 (not in the alphabet)
    0, //   5 (not in the alphabet)
    0, //   6 (not in the alphabet)
    0, //   7 (not in the alphabet)
    0, //   8 (not in the alphabet)
    0, //   9 (not in the alphabet)
    1, //  10 '\n'
    0, //  11 (not in the alphabet)
    0, //  12 (not in the alphabet)
    0, //  13 (not in the alphabet)
    0, //  14 (not in the alphabet)
    0, //  15 (not in the alphabet)
    0, //  16 (not in the alphabet)
    0, //  17 (not in the alphabet)
    0, //  18 (not in the alphabet)
    0, //  19 (not in the alphabet)
    0, //  20 (not in the alphabet)
    0, //  21 (not in the alphabet)
    0, //  22 (not in the alphabet)
    0, //  23 (not in the alphabet)
    0, //  24 (not in the alphabet)
    0, //  25 (not in the alphabet)
    0, //  26 (not in the alphabet)
    0, //  27 (not in the alphabet)
    0, //  28 (not in the alphabet)
    0, //  29 (not in the alphabet)
    0, //  30 (not in the alphabet)
    0, //  31 (not in the alphabet)
    2, //  32 ' '
    67, //  33 '!'
    72, //  34 '"'
    83, //  35 '#'
    95, //  36 '$'
    96, //  37 '%'
    84, //  38 '&'
    71, //  39 "'"
    74, //  40 '('
    75, //  41 ')'
    78, //  42 '*'
    76, //  43 '+'
    66, //  44 ','
    73, //  45 '-'
    65, //  46 '.'
    81, //  47 '/'
    3, //  48 '0'
    4, //  49 '1'
    5, //  50 '2'
    6, //  51 '3'
    7, //  52 '4'
    8, //  53 '5'
    9, //  54 '6'
    10, //  55 '7'
    11, //  56 '8'
    12, //  57 '9'
    69, //  58 ':'
    70, //  59 ';'
    79, //  60 '<'
    77, //  61 '='
    80, //  62 '>'
    68, //  63 '?'
    82, //  64 '@'
    41, //  65 'A'
    58, //  66 'B'
    50, //  67 'C'
    48, //  68 'D'
    39, //  69 'E'
    54, //  70 'F'
    55, //  71 'G'
    46, //  72 'H'
    43, //  73 'I'
    61, //  74 'J'
    60, //  75 'K'
    49, //  76 'L'
    52, //  77 'M'
    44, //  78 'N'
    42, //  79 'O'
    57, //  80 'P'
    63, //  81 'Q'
    47, //  82 'R'
    45, //  83 'S'
    40, //  84 'T'
    51, //  85 'U'
    59, //  86 'V'
    53, //  87 'W'
    62, //  88 'X'
    56, //  89 'Y'
    64, //  90 'Z'
    88, //  91 '['
    86, //  92 '\\'
    89, //  93 ']'
    94, //  94 '^'
    85, //  95 '_'
    93, //  96 '`'
    15, //  97 'a'
    32, //  98 'b'
    24, //  99 'c'
    22, // 100 'd'
    13, // 101 'e'
    28, // 102 'f'
    29, // 103 'g'
    20, // 104 'h'
    17, // 105 'i'
    35, // 106 'j'
    34, // 107 'k'
    23, // 108 'l'
    26, // 109 'm'
    18, // 110 'n'
    16, // 111 'o'
    31, // 112 'p'
    37, // 113 'q'
    21, // 114 'r'
    19, // 115 's'
    14, // 116 't'
    25, // 117 'u'
    33, // 118 'v'
    27, // 119 'w'
    36, // 120 'x'
    30, // 121 'y'
    38, // 122 'z'
    90, // 123 '{'
    87, // 124 '|'
    91, // 125 '}'
    92, // 126 '~'
    0, // 127 (not in the alphabet)
];
