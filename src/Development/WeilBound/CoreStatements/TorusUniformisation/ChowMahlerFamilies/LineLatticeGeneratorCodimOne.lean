module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemRegAtOfCodimOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.line_lattice_generator_codim_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → t ≠ 0 → (∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → L.IsGenAt q t) → L.IsGenAt p t := by
  intro X Ω _ ξ _ hg hn L T p t hL hT ht hq
  obtain ⟨U, hU, b, -, h⟩ := hL p (hT p specializes_rfl)
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  have hgen : ∀ q : Cpt ξ, q.1 ⤳ p.1 → b 0 ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {b 0} := by
    intro q hqp
    obtain ⟨h1, h2⟩ := h q (hT q hqp) (hqp.mem_open U.2 hU)
    exact ⟨h1.ne_zero 0, by rw [h2, hr]⟩
  obtain ⟨he, hp⟩ := hgen p specializes_rfl
  have hu : ∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → unitAt ξ q (t / b 0) := by
    intro q hqp hd
    obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq ht ((hq q hqp hd).2.symm.trans (hgen q hqp).2)
    rwa [e, smul_eq_mul, mul_div_cancel_right₀ _ he]
  have h1 : t / b 0 ∈ regAt ξ p :=
    mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hd => (hu q hqp hd).2.1
  have h2 : (t / b 0)⁻¹ ∈ regAt ξ p :=
    mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hd => (hu q hqp hd).2.2
  refine ⟨ht, ?_⟩
  rw [hp]
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · refine ⟨⟨_, h2⟩, ?_⟩
    change (t / b 0)⁻¹ * t = b 0
    field_simp
  · refine ⟨⟨_, h1⟩, ?_⟩
    change (t / b 0) * b 0 = t
    field_simp
