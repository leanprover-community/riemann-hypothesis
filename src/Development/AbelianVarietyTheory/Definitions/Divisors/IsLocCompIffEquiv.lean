module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def SoleTerm {ι : Type} (C : ι → ℂ) (p q : ι → Prop) : Prop :=
  ∃ i, C i ≠ 0 ∧ p i ∧ ∀ i', C i' ≠ 0 → q i' → i' = i

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isLocComp_iff_equiv {ρc : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : ρc.IsLocComp w σ)
    (τ : SmIrr (GLw n w)) : ρc.IsLocComp w τ ↔ Nonempty (τ.ρ.Equiv σ.ρ) :=
  ⟨fun h' => GlobalTheory.CuspRep.LocUniq.isLocComp_unique ρc w τ σ h' h,
    fun ⟨e⟩ => h.congr ((CuspSub.setoid E n).iseqv.refl ρc) ⟨e.symm⟩⟩

end GlobalTheory.BCT
