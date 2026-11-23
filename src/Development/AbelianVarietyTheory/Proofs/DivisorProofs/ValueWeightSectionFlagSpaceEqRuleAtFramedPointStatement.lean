module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal


theorem _root_.GlobalTheory.T.value_weightSection_flagSpace_eq_rule_at_framedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  first | exact @GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | exact GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | (intros; apply GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR <;> assumption)
