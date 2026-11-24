module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.objTri_of :
    ObjTri := by
  intro p _ D R _ b N hN hNp S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g
  refine ⟨fun m m' => GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp _ _ _ _ _ _ f m m', ?_⟩
  intro fg h m₁₃ m₂₃
  subst h
  obtain ⟨m₁₂⟩ := GlobalTheory.UPel.HT.MapComp.cancel m₁₃ m₂₃
  obtain ⟨c, hc⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁₂ m₂₃
  exact ⟨m₁₂, by rw [← hc]; exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp _ _ _ _ _ _ _ c m₁₃⟩
