module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelElement_at_bad_primes_integral_and_near : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)) (κ' : (I.stp u a i).G c.1), (I.stp u a i).gam c.1 κ' = 1 → PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * x * k (chOf c)) ((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1 → ∀ P : SBof I a, (∀ r s, IntAtA (F := B.host.F) (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) ((((k (chOf c))⁻¹ * x * k (chOf c) : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s)) ∧ (∀ r s, IntAtA (F := B.host.F) (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) (((((k (chOf c))⁻¹ * x * k (chOf c))⁻¹ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s)) ∧ ∀ g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), LiftsInv I κ' P g → GlobalTheory.TwU.NearAt (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((k (chOf c))⁻¹ * x * k (chOf c)) (GlobalTheory.TwU.seamGL (sm I l Z) g) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.ReadBad.main | exact GlobalTheory.Mem.Col2.AdT.ReadBad.main | (intros; apply GlobalTheory.Mem.Col2.AdT.ReadBad.main <;> assumption)
