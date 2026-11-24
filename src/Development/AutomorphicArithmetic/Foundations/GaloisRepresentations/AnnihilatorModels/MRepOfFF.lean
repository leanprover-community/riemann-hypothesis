module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.repOfFF_of :
    AlgOf → RepOfFF := by
  rintro hA κ _ A P ⟨K, i, hm, hfin, hfl, hP⟩
  obtain ⟨B, _, _, k, hf, hfr, pb⟩ := hA (Sp κ) K.left K.hom hfin hfl κ (𝟙 _)
  have hk : IsIso k := pb.isIso_fst_of_isIso
  have hw : k ≫ K.hom = spMap (algebraMap κ B) := by
    simpa using pb.w
  let e : algPt κ B ≅ K := Over.isoMk (asIso k) hw
  refine ⟨Module.finrank κ B, B, ‹_›, ‹_›, hf, hfr, rfl, e.hom ≫ i, inferInstance, fun T g => ?_⟩
  rw [← hP T g]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.hom, by simpa using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.inv, by simpa using hy⟩
