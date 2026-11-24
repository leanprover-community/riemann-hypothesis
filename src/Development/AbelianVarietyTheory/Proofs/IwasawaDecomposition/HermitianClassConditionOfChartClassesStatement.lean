module

public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
public import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClasses
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianClassCondition_of_chartClasses : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  first | exact @GlobalTheory.HermTransport.classTie_of_chart | exact GlobalTheory.HermTransport.classTie_of_chart | (intros; apply GlobalTheory.HermTransport.classTie_of_chart <;> assumption)
