import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.LayerTwoModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G

theorem isRecG_retie {sc D Gt c H F} (h : IsRecG sc D Gt c H F) (g') : IsRecG sc D Gt c ⟨H.lev0, g'⟩ F := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨D0, Lc, I, ψ, hd, ⟨_, g'⟩, hL, _, B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩

theorem gatNum_of_isRecG {sc D Gt c H F} (h : IsRecG sc D Gt c H F) : GatNum sc D := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  intro u w hg
  exact ⟨rfl, rfl⟩


section Stages
variable {B : Base} {C : Cols B} (W W' : RowsRest B C) (V : DivStage B C W) (V' : DivStage B C W') (S : SStage B C W)
  (S' : SStage B C W') (N : NStage B C W) (N' : NStage B C W') (G G' : GJStage B C)





end Stages

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}




theorem exists_over (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ v.asIdeal := by
  have hu : ¬ IsUnit (p : 𝓞 L) := fun h => by
    have h1 := h.map (Algebra.norm ℤ)
    rw [show (p : 𝓞 L) = algebraMap ℤ (𝓞 L) p by simp, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne',
      Int.isUnit_iff_natAbs_eq] at h1
    exact hp.one_lt.ne' (by simpa using h1)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 L)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hp' : (p : 𝓞 L) ∈ M := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨M, hM.isPrime, fun h => hp.ne_zero (by rw [h] at hp'; exact_mod_cast (Ideal.mem_bot.1 hp'))⟩, hp'⟩

theorem under_mem (w : ColW B f T) {p : ℕ} {v : HeightOneSpectrum (𝓞 B.host.F)} (hv : (p : 𝓞 B.host.F) ∈ v.asIdeal) :
    (p : 𝓞 B.host.K) ∈ ((show HeightOneSpectrum (𝓞 B.host.E) from w.I.sel v).under (𝓞 B.host.K)).asIdeal := by
  have h := w.ok.sel_ok v
  rw [← h] at hv
  have h1 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (p : 𝓞 B.host.F) ∈ (w.I.sel v).asIdeal := hv
  show algebraMap (𝓞 B.host.K) (𝓞 B.host.E) (p : 𝓞 B.host.K) ∈ (w.I.sel v).asIdeal
  rw [map_natCast] at h1 ⊢
  exact h1


theorem gIs2_iff (w : ColW B f T) (G : GJStage B w.C) : GIs2 K w G ↔
    ∀ W V S N, Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩) :=
  ⟨fun h W V S N => ⟨(h W V S N).1, (h W V S N).2.2⟩,
    fun h W V S N => let ⟨a, ⟨t⟩⟩ := h W V S N; ⟨a, gatNum_of_isRecG t.isRec, ⟨t⟩⟩⟩


end GlobalTheory.Mem.Top.Bl.LayerTwoModel

end
