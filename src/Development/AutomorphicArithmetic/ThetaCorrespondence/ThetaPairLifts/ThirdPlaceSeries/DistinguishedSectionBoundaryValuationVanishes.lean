module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalk
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset

@[expose] public section



section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KeyValZero
section Key
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Key
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem covers_distinguished_section_valuation_eq_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) 0 1), vV T.V (evI y' t.sig) = 0 := by
  intro _ h2 _ _
  refine h2.imp fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, -⟩ := h
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY Z TF y T io y' g _ hpt hZ => ?_⟩
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  obtain ⟨t, ht⟩ := twSec_keyRoot_val _ _ _ _ _ _ _ Y.U (xiR (Fm.D x ι)) hY.1.unf hY.1.xiAbs hY.1.geo hL.pos hL.good Z
  refine ⟨t, ht T io y' (fun a => ?_) hZ⟩
  letI := io.toAlgebra
  have h1 := ptY_str TF.X y'.1
  rw [hpt, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc] at h1
  obtain ⟨b, hb⟩ := Spec.map_surjective
    (Spec.map (CommRingCat.ofHom g) ≫ ((Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ≫ flagStr TF.X)
  rw [← hb, ← Spec.map_comp] at h1
  exact ⟨b.hom a, congrArg (fun q => CommRingCat.Hom.hom q a) (Spec.map_injective h1)⟩
end GlobalTheory.KeyValZero
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.distinguished_section_boundary_valuation_eq_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) 0 1), vV T.V (evI y' t.sig) = 0 := by
  exact @_root_.GlobalTheory.KeyValZero.covers_distinguished_section_valuation_eq_zero
end
end
