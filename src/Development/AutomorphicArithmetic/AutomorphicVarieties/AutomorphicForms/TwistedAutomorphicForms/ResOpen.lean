module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

@[expose] public section

open ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af Formalism.ConjugateSelfDual UpperTheory.V.Base

theorem UpperTheory.V.Af.Tw.resOpen :
    UpperTheory.V.Af.Tw.ResOpen := by
  unfold UpperTheory.V.Af.Tw.ResOpen
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _
  have hre : resG F L Ω = UpperTheory.V.Base.galEmb F L Ω := rfl
  obtain ⟨hemb, hop, hidx⟩ := UpperTheory.V.Base.galEmbTop F L Ω
  rw [hre]
  refine ⟨⟨hemb, ?_⟩, ?_⟩
  · rw [← MonoidHom.coe_range, UpperTheory.V.Base.range_galEmb]
    exact hop
  · rw [UpperTheory.V.Base.range_galEmb]
    exact hidx
