module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxPowerBasic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.SquarePol

variable {S : Scheme.{0}}

def sqIsPowGrp (G : Over S) [GrpObj G] : Out.IsPowGrp (G ⊗ G) G 2 where
  pr := ![fst G G, snd G G]
  hom := fun i => by
    fin_cases i
    · exact inferInstanceAs (IsMonHom (fst G G))
    · exact inferInstanceAs (IsMonHom (snd G G))
  lim := Fan.IsLimit.mk _ (fun s => lift (s.proj 0) (s.proj 1))
    (fun s i => by
      fin_cases i
      · exact lift_fst _ _
      · exact lift_snd _ _)
    (fun s m hm => by
      apply CartesianMonoidalCategory.hom_ext
      · exact (hm 0).trans (lift_fst _ _).symm
      · exact (hm 1).trans (lift_snd _ _).symm)

def sqPol (P : Out.PolAV S) : Out.PolAV S :=
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI : ∀ i, IsMonHom ((sqIsPowGrp P.A).pr i) := (sqIsPowGrp P.A).hom
  { A := P.A ⊗ P.A
    isAb := (PowGrp.powers S _ P.A 2 (sqIsPowGrp P.A)).2.2.2.1 P.isAb
    g := 2 * P.g
    smoothDim := (PowGrp.powers S _ P.A 2 (sqIsPowGrp P.A)).2.2.1 P.g P.smoothDim
    L := Out.boxLB P.L (sqIsPowGrp P.A).pr
    isLB := DVR.linComb_isLB _ P.isLB _ _
    rigid := by
      obtain ⟨r, hr⟩ := P.rigid
      exact ⟨_, BoxPower.boxRig_isGen (sqIsPowGrp P.A) P.L r hr⟩
    sym := BoxPower.sym_box _ _ P.sym
    ample := relAmple_boxLB S _ P.A 2 (sqIsPowGrp P.A) P.L P.isLB P.ample
    ktriv := kTriv_boxLB S _ P.A 2 (sqIsPowGrp P.A) P.L P.isLB P.ktriv }

theorem sqPol_L (P : Out.PolAV S) :
    (sqPol P).L = LB.LinComb P.L (K := Fin 2) ![(fst P.A P.A).left, (snd P.A P.A).left] ![1, 1] := by
  simp only [sqPol, Out.boxLB]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem exists_square : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), ∃ (P₂ : Out.PolAV (Sp K)) (e : P₂.A ≅ P.A ⊗ P.A), IsMonHom (e.hom ≫ fst P.A P.A) ∧ IsMonHom (e.hom ≫ snd P.A P.A) ∧ P₂.g = 2 * P.g ∧ LBIso P₂.L (LB.LinComb P.L (K := Fin 2) ![(e.hom ≫ fst P.A P.A).left, (e.hom ≫ snd P.A P.A).left] ![1, 1]) := by
  intro K _ _ P
  refine ⟨sqPol P, Iso.refl _, ?_, ?_, rfl, ?_⟩
  · show IsMonHom (𝟙 (P.A ⊗ P.A) ≫ fst P.A P.A)
    rw [Category.id_comp]
    exact (sqIsPowGrp P.A).hom 0
  · show IsMonHom (𝟙 (P.A ⊗ P.A) ≫ snd P.A P.A)
    rw [Category.id_comp]
    exact (sqIsPowGrp P.A).hom 1
  · show LBIso (sqPol P).L (LB.LinComb P.L (K := Fin 2)
      ![(𝟙 (P.A ⊗ P.A) ≫ fst P.A P.A).left, (𝟙 (P.A ⊗ P.A) ≫ snd P.A P.A).left] ![1, 1])
    simp only [Category.id_comp]
    have h : LBIso (sqPol P).L (sqPol P).L := ⟨idIso _, idIso_isGen (sqPol P).isLB⟩
    rw [sqPol_L] at h ⊢
    exact h

end GlobalTheory.SquarePol
