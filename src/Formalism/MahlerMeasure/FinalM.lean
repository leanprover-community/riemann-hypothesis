import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelSum
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeInto
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeBij
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeY
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelDecomp
import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
import Formalism.MahlerMeasure.QuotientUpperBoundsOfPowerBounds

section
namespace Formalism.GM

def LevelConst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a r o n z j : ℕ), 1 ≤ a → 1 ≤ r → o + n + z + 1 ≤ 8 * a →
    j ≤ o → j ≤ n →
    |((padicValRat p
        (((j.factorial ^ 2 * (o + n + r + z + 1 - 2 * j + j - 1).choose j * z.factorial *
            (o - j).factorial * (n - j).factorial : ℕ) : ℚ) /
          (((z + o).factorial * n.factorial : ℕ) : ℚ)) : ℤ) : ℝ)| ≤ 3 * lgV2 p a r

end Formalism.GM
end

section
namespace Formalism.GM.Top
open Formalism.GM
theorem levelAct : LevelAct := levelAct_of alternatingChooseSum
end Formalism.GM.Top
end
