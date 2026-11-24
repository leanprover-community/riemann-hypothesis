module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.HostFrameEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GenHost
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SeedCl
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

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.host_ex :
    GC.Hypotheses₂ → HostFrameEx := by
  intro hP Ω _ _ _ l _ c _ N _ e ψ o₁ hD σ hσ B hB
  obtain ⟨Hb, hG⟩ := gen_host Ω l c N e ψ o₁ hD σ hσ B hB
  obtain ⟨Q, hQ, hS⟩ := seed_cl Ω l c _ _ σ B _ Hb hG
  obtain ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, w, ⟨k, -⟩, hok, hbig, hw, hwQ, hle⟩ := frame_ex hP l _ _ σ B _ Hb hG Q hQ
  refine ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, ⟨k⟩, hok, hbig, hS L w k.ab k.gal hw hwQ hle ?_⟩
  obtain ⟨h, hg⟩ := k.g0
  refine ⟨g₁, ?_, ?_⟩
  · rw [k.gal]
    refine ⟨h, ?_⟩
    have h1 := k.del ⟨g₁, h⟩
    rw [hg] at h1
    exact h1.symm.trans Φ.g0.2
  · have h1 := k.psi ⟨g₁, h⟩
    rw [hg] at h1
    have h2 := hok.baseSubgroup_spec
    rw [h1] at h2
    exact h2
