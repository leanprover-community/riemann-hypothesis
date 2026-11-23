module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimesOfChartFormStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KLeSubOneOfLt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepth2Run
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepthLevelRun
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem GlobalTheory.RunDepth.leafDepth_all_run : (∀ (p : ℕ) [Fact p.Prime], AvFSt p) → (∀ (p : ℕ) [Fact p.Prime], HTFSt p) → (∀ (p : ℕ) [Fact p.Prime], UpFSt p) → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → C0 ≤ oc.C → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → LeafDepthGood N O ∧ LeafDepthRam N O ∧ LeafDepth2 N O ∧ LeafDepthLevel N O := by
  intro hAv hHT hUp
  obtain ⟨C0, hG⟩ := GlobalTheory.T.depthTable_goodPrimes_of_chartForm hUp
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg hSz hx hb tF hC hn he
  exact ⟨hG D L Pm Tp hK T hM EX K Bs Df S P oc O ι N hR hC hPg hSz hn he hx hb tF,
    GlobalTheory.RunDepth.leafDepthRam_run D L Pm Tp hK T EX K Bs Df S P oc O ι N hM hR hPg hSz hx hb tF,
    GlobalTheory.RunDepth.leafDepth2_run hAv hHT D L Pm Tp hK T EX K Bs Df S P oc O ι N hM hR hPg hSz hx hb tF,
    GlobalTheory.RunDepth.leafDepthLevel_run D L Pm Tp hK T EX K Bs Df S P oc O ι N hM hR hPg hSz hx hb tF⟩
