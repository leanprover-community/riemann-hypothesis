module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameChartVectorsCompactFlagSpaceAffi
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt

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


theorem _root_.GlobalTheory.T.exists_eigenFrame_chartVectors_compactFlagSpace_affine : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(Y₀ TF.X Z, W)), (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ → ∀ (k : TF.X.F.J) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (x' : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.Y.X) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x'), ∃ fr : GlobalTheory.ShFam.EigFrame TF.Y φ x', ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt k _ hz hx τ j)).left := by
  first | exact @GlobalTheory.CompHS.exists_eigFrame_vecAt₀ | exact GlobalTheory.CompHS.exists_eigFrame_vecAt₀ | (intros; apply GlobalTheory.CompHS.exists_eigFrame_vecAt₀ <;> assumption)
