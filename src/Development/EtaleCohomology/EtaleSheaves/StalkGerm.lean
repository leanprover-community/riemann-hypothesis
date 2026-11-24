module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ZLGPf

variable {Y X S : Scheme.{0}}

abbrev overO (p : X ⟶ S) (U : S.Opens) : Scheme.{0} := pullback p U.ι

abbrev resO (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : overO p V ⟶ overO p U :=
  pullback.map p V.ι p U.ι (𝟙 _) (S.homOfLE h) (𝟙 _) (by simp) (by simp)

abbrev fO (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) : overO (f ≫ p) U ⟶ overO p U :=
  pullback.map (f ≫ p) U.ι p U.ι f (𝟙 _) (𝟙 _) (by simp) (by simp)

def Germ (q : ℕ) (i n : ℤ) (f : Y ⟶ X) (p : X ⟶ S) (s : S) : Prop :=
  (∀ (U : S.Opens), s ∈ U → ∀ x : Ht q (sch.obj (overO p U)) n i, pull _ (sch.map (fO f p U)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ (U : S.Opens), s ∈ U → ∀ y : Ht q (sch.obj (overO (f ≫ p) U)) n i,
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ ∃ x : Ht q (sch.obj (overO p V)) n i,
      pull _ (sch.map (fO f p V)) _ _ x = pull _ (sch.map (resO (f ≫ p) h)) _ _ y)

def StalkGerm : Prop := Cont → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, ∀ s : S,
  Eqv _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) →
  ∀ n : ℤ, Germ q i n f p s

def ZarInd : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, (∀ (s : S) (n : ℤ), Germ q i n f p s) → Eqv _ (sch.map f) (tw q i)

theorem ZLG_of (hC : Cont) (hM : MV) (h1 : StalkGerm) (h2 : ZarInd) : ZLG := by
  intro hH q Y X S f p _ _ _ _ _ _ hq i hs
  exact h2 hM hH q f p hq i fun s n => h1 hC hH q f p hq i s (hs s) n

end LateralTheory.E.ZLGPf
