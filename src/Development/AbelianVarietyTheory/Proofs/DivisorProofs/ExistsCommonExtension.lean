import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupCLeISupGeneric
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS

open NumberField IsDedekindDomain TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt GlobalTheory.FlagTan

theorem finite_of_finRes {T₀ T : CDVR} (hT : T.FinRes) (g : T₀.V →+* T.V) (hg : Function.Injective g)
    [IsLocalHom g] : g.Finite := by
  letI := g.toAlgebra
  haveI : Finite (T.V ⧸ maximalIdeal T.V) := hT
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  refine GlobalTheory.finite_of_forall_prime_mem (R := T₀.V) (B := T.V) hp.ne_zero (fun P hP h0 => ?_) ?_ ?_
  · rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hp.not_isUnit
  · exact fun h => IsDiscreteValuationRing.not_a_field _ ((Ideal.map_eq_bot_iff_of_injective hg).1 h)
  · exact ne_top_of_le_ne_top (maximalIdeal.isMaximal T.V).ne_top (map_maximalIdeal_le g)


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [NumberField K] [Algebra c.F K] {y : FrPt Xo c K}
  {v : FinitePlace K}

theorem FinFr.exists_baseChange (F : FinFr y v) {W : CDVR} (i : F.T.Fr →+* W.Fr) {r : ℕ} (hr : 0 < r)
    (hi : ∀ x, vV W.V (i x) = (r : ℤ) * vV F.T.V x) (io : c.F →+* W.Fr) (φ : CoefHom c io K)
    (hφ : ∀ a, i (F.φ a) = φ a) : ∃ z : IntFr Xo c W io, letI := io.toAlgebra
      Reframes φ y (fun k => Units.map (i : F.T.Fr →* W.Fr) (F.t k)) z.1 := by
  obtain rfl : i.comp F.io = io := RingHom.ext fun a => by
    letI := io.toAlgebra
    exact (congrArg i (F.φ.commutes a).symm).trans ((hφ _).trans (φ.commutes a))
  letI := (i.comp F.io).toAlgebra
  obtain ⟨z, ψ, hψ, hz⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c F.T W F.io F.pt i r hr
    fun a _ => hi a
  obtain rfl : ψ = ⟨i, fun _ => rfl⟩ := AlgHom.ext (RingHom.congr_fun hψ)
  obtain ⟨w, h₁, h₂⟩ := F.tri
  obtain ⟨w', hw'⟩ := exists_frMap (⟨i, fun _ => rfl⟩ : F.T.Fr →ₐ[c.F] W.Fr) w
  exact ⟨z, w', frMap_comp h₁ hw' hφ, GlobalTheory.SupGeneric.frBor_of_frMap _ h₂ hw' hz⟩





end GlobalTheory.CompHS
