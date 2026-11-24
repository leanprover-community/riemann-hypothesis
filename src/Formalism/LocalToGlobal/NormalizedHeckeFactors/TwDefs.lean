module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions
open scoped NNReal

namespace Formalism.L2.TwC

section rings

variable (l : ℕ) [Fact l.Prime]

def intOf (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : Subring (PadicAlgCl l) :=
  K.toSubalgebra.toSubring ⊓ (PadicAlgCl.valued l).v.integer

def clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) : Subring ℂ_[l] :=
  (F.toSubalgebra.toSubring.map (algebraMap (PadicAlgCl l) ℂ_[l])).topologicalClosure ⊓
    (PadicComplexInt l).toSubring

def Kt (K₀ L : Loc.FinExt l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  K₀.1 ⊔ L.1 ⊔ Loc.MaximalUnramifiedExtension l

def muK (k : ℕ) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] {x | x ^ (l ^ k) = 1}

end rings

section places

theorem placesOver_finite' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hp' : ((p : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hI : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hp'
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  show v.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 E)}
  rw [Ideal.dvd_span_singleton]
  exact hv

def pDC {R : Ranks} (H : Host R) (l : ℕ) : Finset (HeightOneSpectrum (𝓞 H.E)) :=
  (placesOver_finite' H.E (if l = H.pde then H.pde' else H.pde)
    (by split_ifs <;> first | exact H.pde'_prime.ne_zero | exact H.pde_prime.ne_zero)).toFinset

theorem coe_pDC {R : Ranks} (H : Host R) (l : ℕ) :
    (pDC H l : Set (HeightOneSpectrum (𝓞 H.E))) = placesOver H.E (if l = H.pde then H.pde' else H.pde) := by
  first
    | exact Set.Finite.coe_toFinset _

end places

end Formalism.L2.TwC
