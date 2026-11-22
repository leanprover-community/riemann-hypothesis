module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
public import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates
public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

open MeasureTheory Matrix Filter Topology NumberField
open scoped ContDiff ComplexOrder nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.S.GramWordSpace

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev GFn {k0 r : ℕ} (L : LocBessel (k0 + 1) r) :=
  Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)

abbrev Sec (k0 : ℕ) := ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ

export Formalism.MainNotions.S.UnitaryLevelOperators (levOf headEl cutF)

namespace Dat

variable {D : D7} {k0 : ℕ} (X : Dat D k0)

end Dat

section Weights

variable {D : D7} {k0 : ℕ} (Gm : GramMap k0 D.R.rS) (X : Dat D k0)

end Weights

section Lattices

variable (D : D7)

end Lattices

section Estimates

variable (D : D7) {k0 : ℕ} (Gm : GramMap k0 D.R.rS)

end Estimates

section TopLevel

variable (D : D7) {k0 : ℕ} (Gm : GramMap k0 D.R.rS)

end TopLevel

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Gm : ∀ k0 r : ℕ, GramMap k0 r)

end Family

end Formalism.MainNotions.S.GramWordSpace

end
