module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.cochain_shortExact_of_injective :
    ∀ (R : Type) [CommRing R] (I : _root_.GlobalTheory.EtC.Cx R), (∀ n, Injective (I.X n)) → ∀ (S : ShortComplex (_root_.GlobalTheory.EtC.Cx R)), S.ShortExact → ∀ n : ℤ, (∀ a : Cochain S.X₁ I n, ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a) ∧ (∀ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = 0 → ∃ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = b) ∧ ∀ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = 0 → c = 0 := by
  intro R _ I hI S hS n
  have hp : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).ShortExact :=
    fun p => hS.map_of_exact _
  have hmono : ∀ p : ℤ, Mono (S.f.f p) := fun p => (hp p).mono_f
  have hepi : ∀ p : ℤ, Epi (S.g.f p) := fun p => (hp p).epi_g
  refine ⟨fun a => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · refine ⟨Cochain.mk (fun p q h => Injective.factorThru (a.v p q h) (S.f.f p)), ?_⟩
    ext p q h
    simp
  · have hb' : ∀ p q (h : p + n = q), S.f.f p ≫ b.v p q h = 0 := by
      intro p q h
      have := Cochain.congr_v hb p q h
      simpa using this
    refine ⟨Cochain.mk (fun p q h =>
      (CokernelCofork.IsColimit.desc' (hp p).gIsCokernel (b.v p q h) (hb' p q h)).1), ?_⟩
    refine Cochain.ext _ _ (fun p q h => ?_)
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
    exact (CokernelCofork.IsColimit.desc' (hp p).gIsCokernel (b.v p q h) (hb' p q h)).2
  · refine Cochain.ext _ _ (fun p q h => ?_)
    have := Cochain.congr_v hc p q h
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at this
    simpa using (cancel_epi (S.g.f p)).mp (this.trans (comp_zero).symm)

end GlobalTheory.EtC
