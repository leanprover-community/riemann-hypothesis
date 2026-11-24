module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.Functor
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.LsQ

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0)


theorem pt_qT (T : Thick (Wc.L l (B.schFn q) ρ (n + 1))) :
    pt (γ := Wc.pd l k n) (p := l) (q := q) (κ := (Wc.res l k n).comp ρ) (qT (F := B.schFn q) (ρ := ρ) hn T) =
      Spec.map (CommRingCat.ofHom (qe T)) ≫ pt (γ := Wc.pd l k (n + 1)) (p := l) (q := q) (κ := (Wc.res l k (n + 1)).comp ρ) T :=
  rfl


theorem inU_qT (T : Thick (Wc.L l (B.schFn q) ρ (n + 1))) {V : X.Opens}
    (hV : InU (γ := Wc.pd l k (n + 1)) (p := l) (q := q) (κ := (Wc.res l k (n + 1)).comp ρ) V T) :
    InU (γ := Wc.pd l k n) (p := l) (q := q) (κ := (Wc.res l k n).comp ρ) V (qT (F := B.schFn q) (ρ := ρ) hn T) := by
  unfold InU at hV ⊢
  rw [pt_qT, Scheme.Hom.comp_preimage, top_le_iff.1 hV]
  simp

theorem hGq (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory) :
    stF q ρ n 𝒱 ((mq (F := B.schFn q) (ρ := ρ) hn).G.obj ⟨T.obj, T.property.1⟩).obj := by
  obtain ⟨-, V, hV, hin⟩ := T.property
  exact ⟨((mq (F := B.schFn q) (ρ := ρ) hn).G.obj ⟨T.obj, T.property.1⟩).property, V, hV, inU_qT q ρ hn T.obj hin⟩

abbrev mqS (𝒱 : Set X.Opens) : QMor (sV q ρ n 𝒱) (sV q ρ (n + 1) 𝒱) (IdF.span _ ((l : WittVector l k) ^ n)) :=
  subQ (mq (F := B.schFn q) (ρ := ρ) hn) (stF q ρ n 𝒱) (stF q ρ (n + 1) 𝒱) (fun _ h => h.1) (hGq q ρ hn 𝒱)

end CrystallineSemistableComparison.Pb.SubquotientResolution

end
