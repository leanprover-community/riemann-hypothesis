module

public import Development.EtaleCohomology.EtaleSheaves.ChartSurjCut
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ChartSurjCut

namespace LateralTheory.E.LCIsoPf

def TwTriv : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), Sec (tw q 0) X ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ x : Sec (tw q 0) X,
      Sec.res f (e X s x) = e Y t (Sec.res f x)

def Tw0 : Prop := ∀ (q : ℕ),
  ∃ c : ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → (LocallyConstant T (ZMod q) ≃+ Sec (tw q 0) T),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (hV : IsUnit (q : Γ(V, ⊤))) (hU : IsUnit (q : Γ(U, ⊤))) (a : LocallyConstant U (ZMod q)),
      Sec.res g (c U hU a) = c V hV (a.comap g.base.hom)

def SecIso : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      Sec.res f (e X s g) = e Y t (g.comap f.base.hom)

theorem unit_of {q : ℕ} {S X : Scheme.{0}} (ζ : Prim q Γ(S, ⊤)) (s : X ⟶ S) : IsUnit (q : Γ(X, ⊤)) :=
  (ζ.map s.appTop.hom).2.1

theorem SecIso_of (hT : TwTriv) (h0 : Tw0) : SecIso := by
  intro q i S ζ
  obtain ⟨eT, heT⟩ := hT q i S ζ
  obtain ⟨c, hc⟩ := h0 q
  refine ⟨fun X s => (c X (unit_of ζ s)).trans (eT X s), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heT s t f hf, hc f (unit_of ζ t) (unit_of ζ s)]

theorem SecIso_LCIso (hS : SecIso) : LCIso := by
  intro H q i S ζ
  obtain ⟨eS, heS⟩ := hS q i S ζ
  obtain ⟨-, eA, heA, -⟩ := H.a9 (ZMod q) (tw q i)
  refine ⟨fun X s => (eS X s).trans (eA X), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heA, heS s t f hf g]

end LateralTheory.E.LCIsoPf
