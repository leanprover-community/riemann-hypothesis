module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem ds_res_map_comm {R : Type} [CommRing R] {Z S : Scheme} (p : Z ⟶ S) {G G' : Shv R}
    (f : G ⟶ G') {W V : Scheme} (k : W ⟶ V) (x : DS p G V) :
    DS.res p G' k (DS.map p f V x) = DS.map p f W (DS.res p G k x) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) (((phiPF p R).map f).naturality k.op)
  simp only [phiPF, phiP, ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  exact h.symm

theorem UpperTheory.Gal.TranscendenceTraces.phiExact_of :
    DSLoc → PhiExact := by
  intro hD R _ Z S p _ T hT
  obtain ⟨-, hmono, -, -, hloc, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  change Sec ((phi p R).obj T.X₂) U at b
  change Sec.map ((phi p R).map T.g) b = 0 at hb
  have h1 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₂)).1 U b
  apply hloc
  apply hmono _ _ _ h1
  rintro V g ⟨x0, hx0⟩
  obtain ⟨x, hx⟩ : ∃ x : DS p T.X₂ V, phiSec p T.X₂ V x = Sec.res g b := ⟨x0, hx0⟩
  have hz : phiSec p T.X₃ V (DS.map p T.g V x) = 0 := by
    rw [← phiSec_map, hx, map_res, hb]
    exact map_zero _
  have h2 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₃)).2.1 V _ hz
  apply hloc
  apply hmono _ _ _ h2
  intro W k hk
  have hk' : DS.res p T.X₃ k (DS.map p T.g V x) = 0 := hk
  have h0 : DS.map p T.g W (DS.res p T.X₂ k x) = 0 := by
    rw [← ds_res_map_comm]
    exact hk'
  apply hmono _ _ _ (hD R p T hT W (DS.res p T.X₂ k x) h0)
  rintro W' k' ⟨a, ha⟩
  refine ⟨phiSec p T.X₁ W' a, ?_⟩
  change Sec.map ((phi p R).map T.f) (phiSec p T.X₁ W' a) = Sec.res ((k' ≫ k) ≫ g) b
  rw [phiSec_map, ha, ← phiSec_res, ← phiSec_res, hx]
  exact (res_res k' k (Sec.res g b)).trans (res_res (k' ≫ k) g b)
