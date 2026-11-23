module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)}
  (K : LevelChart (I.rec7 l Z) ((I.rec7 l Z).mem u).A.T (badG (I.rec7 l Z)) i hi stab lat)
  {Hs : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g a : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin ((I.rec7 l Z).R.N i)) (kv (I.rec7 l Z).host.F v))} {lam : ∀ a v h, Hs a v h →* ℂˣ},
  GLevH K.lev F.gl Hs lam → (∀ x, x ∈ K.lev.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N i) (X.piT u)) →
  ∃ L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f,
    K.lev.Lb = reL (rankN (I.rec7 l Z) i hi) L.Lb ∧
    (∀ v, K.lev.Uloc v = (L.Uloc v).map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom) ∧
    K.lev.U = L.U.map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom := by
  first | exact @GlobalTheory.Mem.Col2.TC.level_of_chart | exact GlobalTheory.Mem.Col2.TC.level_of_chart | (intros; apply GlobalTheory.Mem.Col2.TC.level_of_chart <;> assumption)
