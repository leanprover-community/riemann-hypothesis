module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRes

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.map φ (Sec.res g y) = Sec.res g (Sec.map φ y) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom y) h

theorem resGood : CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.KapBij → CrystallineSemistableComparison.E.ResZero → CrystallineSemistableComparison.E.ResSplit → CrystallineSemistableComparison.E.ResGood := by
  intro hS hB hZ hX hgen q _ C _ P i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c c' φ x
    have h1 := (hS q i (P.U c) (P.ζ c) x).2.2 (P.U c') (P.S.map φ).unop
    rw [P.ζ_nat φ] at h1
    have h2 := sec_map_res (resι _ (tw q i)) (P.S.map φ).unop (kap i (P.ζ c) x)
    rw [h1] at h2
    exact h2
  · intro s c c' φ x
    exact sec_map_res ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (P.S.map φ).unop x
  · intro c a b h
    exact (hB hgen q i (P.U c) (P.ζ c)).1 ((hZ _ (tw q i) (P.U c)).1 h)
  · intro c y
    have h := (hZ _ (tw q i) (P.U c)).2.1 y
    constructor
    · intro h0
      obtain ⟨t, ht⟩ := h.1 h0
      obtain ⟨f, hf⟩ := (hB hgen q i (P.U c) (P.ζ c)).2 t
      exact ⟨f, by rw [← ht, ← hf]; rfl⟩
    · rintro ⟨f, rfl⟩
      exact h.2 ⟨_, rfl⟩
  · intro s c
    exact hX _ (tw q i) (P.U c) (P.split c) s

end GlobalTheory.CompanionTheory.EdgeRes
