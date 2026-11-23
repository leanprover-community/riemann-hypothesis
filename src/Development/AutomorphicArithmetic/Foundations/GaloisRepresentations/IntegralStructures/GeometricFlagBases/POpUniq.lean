module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem l_unit (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) (Ω : Type) [Field Ω] [Algebra k Ω] :
    IsUnit (l : Γ(G3.sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap k Ω)]
    exact (_root_.map_ne_zero _).mpr hl
  have h3 := h1.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa [map_natCast] using h3

theorem UpperTheory.Gal.Int.Geo.opUniq_of :
    G3.HopSpec → G3.OpEx.{1} → G3.OpEt → G3.EtGood → G3.BcSplits → OpUniq := by
  intro hHop hEx hEt hGood hBc l _ k _ hl H Ω _ _ g d hd T hT
  obtain ⟨hhop, -⟩ := hHop l hl H Ω g d hd
  have hsplit : G3.GalSplit (H.sΩ Ω g) := by
    unfold GlobalTheory.GalV.IsCorrOp at hT
    unfold G3.GalSplit
    obtain ⟨W, c, G, i1, i2, a, J, i3, σ, hG, hS, -⟩ := hT
    exact ⟨W, c, G, i1, i2, a, J, i3, σ, hG, hS⟩
  have hgood := hGood l (G3.sp Ω) (l_unit l hl Ω)
  haveI : IsFinite (H.s g) := hd.1
  haveI : Etale (H.s g) := hd.2.1
  have hbc := hBc (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) H.q (H.s g ≫ H.q) H.q (H.s g) rfl
    (𝟙 _) (Category.id_comp _) Empty (fun e => e.elim) (fun e => e.elim)
  haveI : IsFinite (H.sΩ Ω g) := hbc.1
  haveI : Etale (H.sΩ Ω g) := hbc.2.1
  let p : H.geomZ Ω ⟶ G3.sp Ω := pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
  have hcomm : H.tΩ Ω g ≫ p = H.sΩ Ω g ≫ p := by
    simp only [p, HTower.sΩ, HTower.tΩ, HTower.geomZ, geom, geomMap]
    erw [pullback.lift_snd, pullback.lift_snd]
  obtain ⟨A, -, huniq⟩ := (hEx (G3.et l (G3.sp Ω)) hgood p p (H.sΩ Ω g) (H.tΩ Ω g) hcomm).1 hsplit
  have h1 := huniq T ((hEt l p p _ _ hcomm T).mpr hT)
  have h2 := huniq (hop l H Ω g) ((hEt l p p _ _ hcomm _).mpr hhop)
  exact h1.trans h2.symm
