module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

open Matrix Formalism.UG ValuativeRel
open scoped TensorProduct
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsUWeilPair)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.LFun (HasSatU)

def str (q : ℂˣ) (n : ℤ) : Multiset ℂˣ := (Multiset.range n.toNat).map fun j : ℕ => q ^ (2 * (j : ℤ) - (n - 1))

section Valued

variable (E : Type) [Field E] [Valued E (WithZero (Multiplicative ℤ))]

variable {E}

variable {n : ℕ}

end Valued

section Local

variable {F : Type} [Field F] {E : Type} [Field E] [Valued E (WithZero (Multiplicative ℤ))] [Algebra F E]
  (c : E →ₐ[F] E) {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

end Local

section Res

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

end Res

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

end
