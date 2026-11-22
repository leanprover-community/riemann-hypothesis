module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.MainNotions.CartierLocalBounds

open Formalism.BasicNotions

section Jets

variable {C : Type} [Field C]

end Jets

attribute [instance] LocD.instTt LocD.modTt

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

end LocD

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

end LocD

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

end LocD

variable (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) (Lc : Loc D X Y)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (YF x hx i))

end Family

end Formalism.MainNotions.CartierLocalBounds
