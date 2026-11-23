module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

theorem snd_transl (x : 𝟙_ (Over S) ⟶ G) :
    (snd (𝟙_ (Over S)) G ≫ transl x).left = (Out.translPt G x).left := by
  congr 1
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (snd (𝟙_ (Over S)) G ≫ toUnit G)
    (fst (𝟙_ (Over S)) G), mul_comm]
  rfl

theorem exists_theta (hL : L.IsLB) (x : 𝟙_ (Over S) ⟶ G)
    (φ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (transl x).left] ![1, -1])) (hφ : φ.IsGen) :
    ∃ θ : Out.ThetaGrp G L 1 (𝟙_ (Over S)), θ.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ 𝟙_ (Over S)) (a : Z ⟶ G)
      (z : Z.left) (J), Good L z J → CommutatorPairing.thetaVal θ t a z J = val φ a.left z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![(snd (𝟙_ (Over S)) G).left, (Out.translPt G x).left]) (ε' := ![1, -1]) (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id]
      rw [← Over.comp_left, snd_transl])
    (LB.pullGen L _ _ φ (snd (𝟙_ (Over S)) G).left) (DVR.pullGen_isGen _ _ _ _ hφ _)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)
  rw [← Over.comp_left, lift_snd]

theorem gen_commute_of_weilIs : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G →
    ∀ (L : LB G.left), L.IsLB → ∀ (x y : 𝟙_ (Over S) ⟶ G)
    (φx : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl x).left] ![1, -1]))
    (φy : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl y).left] ![1, -1])),
    φx.IsGen → φy.IsGen → Out.WeilIs G L 1 x y 1 →
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ φx (LB.pullGen L _ _ φy (GlobalTheory.UPel.HT.Hecke.transl x).left))
      (LB.mulGen L _ _ _ _ φy (LB.pullGen L _ _ φx (GlobalTheory.UPel.HT.Hecke.transl y).left)) := by
  intro S G _ _ hA L hL x y φx φy hx hy hW
  obtain ⟨θx, hθx, ex⟩ := exists_theta hL x φx hx
  obtain ⟨θy, hθy, ey⟩ := exists_theta hL y φy hy
  rw [← hθx, ← hθy] at hW
  have hC := (GlobalTheory.CommutatorPairing.commIsOf_iff hL θx θy 1).1
    ((GlobalTheory.GlobalLift.weilIs_iff_commIsOf GlobalTheory.globalFns_holds hA hL θx θy 1).1 hW)
  refine corr_of_val hL fun g J hJ => ?_
  have h := hC G (toUnit G) (𝟙 G) g J hJ
  rw [map_one, CommutatorPairing.commVal, mul_inv_eq_one, ex _ _ _ _ _ hJ, ex _ _ _ _ _ hJ, ey _ _ _ _ _ hJ,
    ey _ _ _ _ _ hJ] at h
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
  rw [hθx, hθy, show toUnit G ≫ x * 𝟙 G = transl x from mul_comm _ _,
    show toUnit G ≫ y * 𝟙 G = transl y from mul_comm _ _] at h
  exact h

end GlobalTheory.UPel.HT.Hecke
