module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.deRhamComponent_wachLetter_basis_filtration : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ ι, Comp (HW l) h i ζ τ ι → τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb i → (∀ (r : ℕ) (d : Fin r → T.V ⊗[ℚ_[l]] (D.loc l).R.B) (b : Fin r → (D.loc l).R.BdR), (∀ a, d a ∈ Di (HW l) h T i) → LinearIndependent ↥LL.1 d → ∑ a, mulVR T (b a) (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (d a)) ∈ compKer T ι → ∀ a, b a = 0) ∧ (∀ d ∈ Di (HW l) h T i, ∀ a : ℤ, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ↔ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ compKer T ι ⊔ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) a) ∧ (∀ w ∈ DdRE ((D.loc l).PD K) T.ρ τ, ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ') ∧
    @Module.finrank ↥LL.1 ↥(Di (HW l) h T i) _ (Submodule.addCommMonoid _) (Submodule.module _) =
      Module.finrank ↥LL.1 T.V := by
  intro D HW l _ K s LL h W T hT i ζ τ ι hC hτ
  obtain ⟨-, -, -, hc, hc0⟩ := Points.points D HW l K s LL h
  exact GlobalTheory.NL.CompD.component_tied (D.locT l) K LL T hc hc0 hT τ ι hC.2.2 _ hτ
