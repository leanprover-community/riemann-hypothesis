module

public import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRingUnitPf
open LateralTheory.E.CupProductRingLaws

def UnitProp {q : ℕ} {i : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))) : Prop :=
  ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b

def LeafUnitPair : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ),
  ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i))), IsTwPair μ ∧ UnitProp μ

def OneLoc {q : ℕ} {E : Spc} (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U), Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g (ev (R := ZMod q) α.1 0 0 (by simp) U x) = resGen 0 ζ)

def LeafOneLoc : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, IsOneCocycle q E α → OneLoc α

def LeafUnitAW : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) (i : ℤ)
  (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))), UnitProp μ →
  ∀ (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0), OneLoc α →
  ∀ (n : ℤ) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n),
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (0 + i))) (0 + n), μ.IsAW rfl α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast (by ring) (by ring) (CohomologyClass.mk β : Ht q E n i)

theorem LeafRingUnit_of (hcup : LeafCupSpec) (hex : LeafTwPairExists) (hun : LeafTwPairUnique) (hone : LeafOneSpec)
    (h1 : LeafUnitPair) (h2a : LeafOneLoc) (h2 : LeafUnitAW) : LeafRingUnit := by
  intro q _ E hE n i a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨μ, hμ, hU⟩ := h1 q i
  obtain ⟨⟨α, hα⟩, hαone⟩ := hone q E hE
  obtain ⟨γ, hγ, hγc⟩ := h2 q E i μ hU α (h2a q E hE α hα) n β
  have htw : IsTwPair (twPair q 0 i) := pick_spec (hex q 0 i)
  have hc : cup q (one q E) (CohomologyClass.mk β) = (twPair q 0 i).cup E rfl (one q E) (CohomologyClass.mk β) := rfl
  rw [hc, hun q 0 i _ μ htw hμ E rfl, hαone α hα, (hcup (ZMod q) μ E rfl).2 α β γ hγ, hγc]

end LateralTheory.E.LeafRingUnitPf
