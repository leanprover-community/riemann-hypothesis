module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_cartierDivisor_det_lieEigenparts_toroidal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)], ∃ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ ∧ ∀ a : (E →+* ℂ) → ℤ, ∃ D : CartierDiv (X₀ TF.Y Z), CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) ∧ ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-a τ)) := by
  first | exact @GlobalTheory.EigDiv.exists_detDiv | exact GlobalTheory.EigDiv.exists_detDiv | (intros; apply GlobalTheory.EigDiv.exists_detDiv <;> assumption)
