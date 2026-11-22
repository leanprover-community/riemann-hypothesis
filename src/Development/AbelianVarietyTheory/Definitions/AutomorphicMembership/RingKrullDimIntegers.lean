module

public import Mathlib
public import Formalism.LocalRingCardinality.DataDIV
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemEqnSetOmegaCoeff
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter MeasureTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

variable {F : Type} [Field F] [NumberField F]

abbrev Pts (Y : Var F) (σ : F →+* ℂ) : Type := CxPts Y.str σ

attribute [instance] CxSt.fnCRing CxSt.fnCAlg

namespace CxSt

variable (C : CxSt F) (Y : Var F) (σ : F →+* ℂ) (Δ : Y.Dv) (m : C.Met Y σ Δ)

end CxSt

abbrev below {K : Type} [Field K] {Z : Scheme.{0}} (y : Sp K ⟶ Z) : Z := y (IsLocalRing.closedPoint K)

open Classical in
def valAt {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (f : Z.functionField) : K :=
  if h : RegAt (below y) f then (Scheme.stalkClosedPointTo y).hom h.choose else 0

instance Ext.instNonempty (v : HeightOneSpectrum (𝓞 F)) : Nonempty (Ext v) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let K := v.adicCompletion F
  have h1 : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1 := (FinitePlace.norm_lt_one_iff_mem F v a).2 ha
  have h0 : FinitePlace.embedding v (algebraMap (𝓞 F) F a) ≠ 0 := by
    simpa using ha0
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨_, h0, h1.ne⟩
  let L := AlgebraicClosure K
  letI : Algebra F L := ((algebraMap K L).comp (FinitePlace.embedding v)).toAlgebra
  let j : AlgebraicClosure F →ₐ[F] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let N := spectralMulAlgNorm K L
  let w : AbsoluteValue (AlgebraicClosure F) ℝ :=
    (MulRingNorm.mulRingNormEquivAbsoluteValue N.toMulRingNorm).comp (f := j.toRingHom) j.injective
  have hw (x) : w x = spectralNorm K L (j x) := rfl
  have hn (x y) : w (x + y) ≤ max (w x) (w y) := by
    rw [hw, hw, hw, map_add (f := _)]; exact isNonarchimedean_spectralNorm _ _
  refine ⟨⟨w, fun x => ?_, ⟨⟨⟨⟨⟨{x | w x ≤ 1}, ?_⟩, by simp⟩, ?_, by simp⟩, ?_⟩, ?_⟩, fun _ => Iff.rfl⟩⟩
  · rw [hw, j.commutes, ← FinitePlace.norm_embedding]
    exact spectralNorm_extends _
  · intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact mul_le_one₀ hx (w.nonneg _) hy
  · intro x y hx hy
    exact (hn x y).trans (max_le hx hy)
  · intro x hx
    simpa using hx
  · intro x
    rcases le_total (w x) 1 with h | h
    · exact .inl h
    · refine .inr ?_
      change w x⁻¹ ≤ 1
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ h

namespace Adl

variable {C : CxSt F} {Y : Var F} (A : Adl C Y)

variable {A}

end Adl

namespace Base

end Base

open Base

namespace Adl

variable {C : CxSt F} {Y : Var F} {A : Adl C Y} {M : Model Y} {L : HermLB M.p} {k : ℕ+}
  {cf : HeightOneSpectrum (𝓞 F) → ℝ}

end Adl

variable [StarRing F]

end GlobalTheory.TrueGeo
