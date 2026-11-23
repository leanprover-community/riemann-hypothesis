module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.HostFrameEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SeedCl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SqrtDiscr
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

theorem UpperTheory.V.Fr.gd_ex :
    GC.Hypotheses₂ → GdFrameEx := by
  intro hP Ω _ _ _ K _ _ _ _ l _ c _ N _ e ψ D B hB
  have hG := gen_gd Ω K l c N e ψ D B hB
  obtain ⟨Q, hQ, hS⟩ := seed_cl Ω l c _ _ _ B _ _ hG
  obtain ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, w, ⟨k, -⟩, hOk, hBig, hw, hwQ, hle⟩ :=
    frame_ex hP l _ _ _ B _ _ hG Q hQ
  refine ⟨L, i1, i2, i3, i4, g₁, Φ, C₀, ⟨k⟩, hOk, hBig, hS L w k.ab k.gal hw hwQ hle ?_⟩
  obtain ⟨h, hg⟩ := k.g0
  refine ⟨g₁, ?_, ?_⟩
  · rw [k.gal]
    refine ⟨h, ?_⟩
    have h1 := k.del ⟨g₁, h⟩
    rw [hg] at h1
    exact h1.symm.trans Φ.g0.2
  · have h1 := k.psi ⟨g₁, h⟩
    rw [hg] at h1
    exact h1 ▸ hOk.baseSubgroup_spec
