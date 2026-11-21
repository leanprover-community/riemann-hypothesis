import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTFinal
import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfEx
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf

namespace Formalism.L2.FormalSeriesBounds




theorem ptSelf_of_start2 (hS : AllStartSelfSt) : PTSelfSt :=
  ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds


end Formalism.L2.FormalSeriesBounds
