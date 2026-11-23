module

public import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.ComplF
public import Formalism.LocalToGlobal.Columns.Inputs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

def WeakApproxU {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : Prop :=
  ∀ x ∈ UAd hc n, ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ ∈ URat hc n,
    IntAt v (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∧
    IntAt v ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))

def GenusToPoint : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E N →
    Formalism.HermitianLatticesTheory.SameGenus (hStd E n) (stdLat E n) N → ∃ x ∈ UAd hc n, Formalism.UG.CS.globLat x (stdLat E n) = N

def PointToGenus : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), WeakApproxU hc n → ∀ x ∈ UAd hc n,
    Formalism.HermitianLatticesTheory.SameGenus (hStd E n) (stdLat E n) (Formalism.UG.CS.globLat x (stdLat E n))

def LocToAd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), UnimodGenusLoc E n → UnimodGenus hc n

def AdToLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), WeakApproxU hc n → UnimodGenus hc n → UnimodGenusLoc E n

def Bridge : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), WeakApproxU hc n → (UnimodGenusLoc E n ↔ UnimodGenus hc n)

end Formalism.L2.GenusGluing.Gen
