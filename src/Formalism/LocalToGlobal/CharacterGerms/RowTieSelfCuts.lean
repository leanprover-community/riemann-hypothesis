module

public import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData
public import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
public import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

end Core

def RankMaximalSelfOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0),
    NDG Y → (Y.rawSelf p).RankHyp → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable (Xo c)

theorem rank_maximal_self_charts_of_nondegenerate (h1 : RankMaximalSelfOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalSelfCharts Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY _ d _ lab ha hg hr o Hc => by
    have hrank : (Y.rawSelf (selfOfLab ha hg o)).RankHyp := by
      refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
      · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab]
          convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.1 a hb) using 2
          exact Finset.filter_congr (fun _ _ => Iff.rfl)
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
          exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.1 a hb)
      · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab]
          convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.2.1 a hb) using 2
          exact Finset.filter_congr (fun _ _ => Iff.rfl)
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
          exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.2 a hb)
    exact h1 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (h2 hstar T io y C3 C V ι hι k Y hY) hrank Hc

end Formalism.L2.FormalSeriesBounds
