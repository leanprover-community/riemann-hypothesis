module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.PrVTensInt
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.AdelicLocalLattice

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def FvStab (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
    γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
    ∀ (v : (D.mem u).A.vT) (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c)))
      (hx : γ.1.1 *ᵥ x.1 ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)),
      (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ ⟨γ.1.1 *ᵥ x.1, hx⟩) =
        (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ x)

theorem stabLF_of_fv (Tf : FormsTiedSym D u Ch chOf) (hF : FvStab Tf) : StabLF Tf :=
  stabLF_of Tf (fun c γ hγ => ⟨stab_lat Tf latLocGlob adelic_local_lattice c γ hγ, hF c γ hγ⟩)

theorem stabiliser_bijective_self_dual
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hF : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      FvStab Tf) : StabiliserMapBijective :=
  stabiliser_bijective_of_finite hSD (fun D u Ch chOf Tf => stabLF_of_fv Tf (hF D u Ch chOf Tf))

end Formalism.L2.GlobalTheoryTheory.Br
