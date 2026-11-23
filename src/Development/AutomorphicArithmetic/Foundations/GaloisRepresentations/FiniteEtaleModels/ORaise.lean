module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.TExt
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private lemma tate_evaluation_nsmul {G : GDatum} {k Q : Type} [Field k] [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso G k Q act e) (n m : ℕ) (x : G.La) : I.ev n (m • x) = I.ev n x ^ m := by
  induction m with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    simpa using h
  | succ m ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.FiniteEtaleModels.O.raise :
    UpperTheory.Gal.FiniteEtaleModels.O.Raise := by
  intro q _ D R R' _ _ _ b gb β hm N N₀ c hN hpos hcop X₁ s₁ u Ω _ _ y σ hyσ
  subst hN
  have hN₀ : 0 < N₀ := Nat.pos_of_mul_pos_right hpos
  have hc : 0 < c := Nat.pos_of_mul_pos_left hpos
  let u1 := GlobalTheory.HTPullEvery.objPull u y (y ≫ s₁) rfl
  let m1 := GlobalTheory.HTPullEvery.objPullMap u y (y ≫ s₁) rfl
  let u2 := GenCmp.rebase (gb := gb) hm.1 hm.2 hyσ u1
  let g0 : GObj gb N₀ σ := GenCmp.toGObj u2 (GenCmp.geomFull hcop u2)
  obtain ⟨β', hβ'⟩ := GenCmp.exists_spMap σ
  obtain ⟨I, hI⟩ := g0.geom Ω (𝟙 _) β' (by rw [Category.id_comp, hβ'])
  have hI' : ∀ z, I.ev N₀ z = g0.eta z := by
    intro z
    rw [← hI z]
    have : toUnit (Over.mk (𝟙 (Sp Ω))) = 𝟙 _ := toUnit_unique _ _
    rw [this, Category.id_comp]
  let o : GObj gb (N₀ * c) σ :=
    { g0 with
      eta := fun z => I.ev (N₀ * c) z
      eta_add := fun x z => I.add _ x z
      eta_lin := fun a z => I.lin _ a z
      eta_ker := fun x => (I.ker _ hpos _).mpr ⟨x, rfl⟩
      geom := by
        intro k _ _ x β₁ hx
        obtain ⟨I₁, hI₁⟩ := UpperTheory.Gal.FiniteEtaleModels.O.tExt _ _ gb _ Ω σ g0 I k x
        refine ⟨I₁, fun z => ?_⟩
        ext
        rw [hI₁ _ hpos z]
        simp }
  have key : ∀ z, Over.Hom.left (o.eta (c • z)) ≫ m1.φ = y ≫ Over.Hom.left (u.eta z) := by
    intro z
    have h1 : o.eta (c • z) = g0.eta z := by
      change I.ev (N₀ * c) (c • z) = g0.eta z
      rw [tate_evaluation_nsmul, I.tower _ _ hN₀ hc, hI']
    rw [h1]
    exact m1.eta z
  exact ⟨o, ⟨⟨m1.φ, m1.φ₂, m1.cart, m1.sq, m1.act, m1.pol, key⟩⟩⟩
