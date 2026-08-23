import PrimParser.Basic

/-!
# Byte parsers
-/

namespace Parser

abbrev ByteParser (ε : Type) (g : Grade) (α : Type) : Type := Parser ByteArray UInt8 ε g α

end Parser
