module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

theorem UpperTheory.Gal.Int.Geo.Pl.congOf_of :
    LevBasic → TjOK → TjIdx → CongOf := by
  intro hL hT hI E _ _ _ A n p _ S F x hx N w σ J L _ g θ ϑ hD hm
  obtain ⟨-, h2, h3, -⟩ := hL p S.D S.G S.L
  obtain ⟨l1, l2, l3, l4, l5⟩ := σ.lv
  refine ⟨σ.q, σ.r, Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, σ.K₀, σ.atp,
    ⟨ordCompl[σ.q] N.1, σ.𝔞, l1, l2, l3, l4, l5, rfl⟩, σ.isLev,
    h2 _ _ _ _ (h3 N.1) σ.isLev ((Ideal.span_singleton_le_iff_mem _).2 σ.mem), σ.mem, hD, ?_⟩
  intro i hi
  obtain ⟨j, ⟨hin, hK, hH, hM⟩, hθ⟩ := hm i hi
  refine ⟨j, hK, (hT E A n p S F x hx N w σ i hin _ hH).2, ?_, ?_, ?_⟩
  · rw [hM]; exact Dvd.intro_left _ rfl
  · intro _
    exact hI E A n p S F x hx N w σ i hin _ hH
  · rw [hθ, idx, hK]
