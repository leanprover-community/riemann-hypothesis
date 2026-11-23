module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisation
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

theorem _root_.GlobalTheory.T.moveDown_levelPrime_adelic_factorisation : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ hβ : chOf ((I.fm l u a).dn i v c.1 g) = β, ∃ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)) (η : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (κ : (K β).lev.U), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) ∧ (∀ v', v' ≠ (eV v).1 → bc (prV (E := (I.rec7 l Z).host.E) v') η.1 = 1) ∧ bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) γ.1 * ((K β).y ⟨(I.fm l u a).dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧ ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) : B.LLˣ) : B.LL) := by
  exact @GlobalTheory.Mem.Col2.DnAdel.move_down_adelic
