module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFrLifts
public import Formalism.LocalToGlobal.Columns.LevGSym

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

section Conv

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

def conv (c c' : WO S T →₀ ℂ) : WO S T →₀ ℂ :=
  ∑ x ∈ c.support, ∑ y ∈ c'.support, Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y))

def convList (l : List (WO S T →₀ ℂ)) : WO S T →₀ ℂ := l.foldr (conv ψ S T) (Finsupp.single 0 1)

theorem comb_conv (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (conv ψ S T c c') f = comb ψ S T c (comb ψ S T c' f) := by
  have h0 := fun u => zero_smul ℂ (heisO ψ S T u f)
  have h1 := fun u (a b : ℂ) => add_smul a b (heisO ψ S T u f)
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum, conv, ← Finsupp.sum_finsetSum_index h0 h1]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finsupp.sum_finsetSum_index h0 h1]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.sum_single_index (h0 _), GlobalTheory.WeilVacMove.heisO_heisO, smul_smul]

theorem comb_unit (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (h := fun u (a : ℂ) => a • heisO ψ S T u f) (zero_smul ℂ _), one_smul]
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem comb_convList {α : Type} (l : List α) (c : α → WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (convList ψ S T (l.map c)) f = l.foldr (fun i f' => comb ψ S T (c i) f') f := by
  induction l with
  | nil => exact comb_unit ψ S T f
  | cons i l ih => exact (comb_conv ψ S T _ _ f).trans (congrArg _ ih)

variable {ψ S T}

theorem mem_support_conv {c c' : WO S T →₀ ℂ} {w : WO S T} (hw : w ∈ (conv ψ S T c c').support) :
    ∃ x ∈ c.support, ∃ y ∈ c'.support, w = x + y := by
  classical
  rw [Finsupp.mem_support_iff, conv, Finsupp.finsetSum_apply] at hw
  obtain ⟨x, hx, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  rw [Finsupp.finsetSum_apply] at h2
  obtain ⟨y, hy, h3⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  have h4 : w ∈ (Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y))).support := Finsupp.mem_support_iff.mpr h3
  exact ⟨x, hx, y, hy, Finset.mem_singleton.1 (Finsupp.support_single_subset h4)⟩

theorem support_convList {p : WO S T → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) {l : List (WO S T →₀ ℂ)}
    (hl : ∀ c ∈ l, ∀ x ∈ c.support, p x) : ∀ w ∈ (convList ψ S T l).support, p w := by
  induction l with
  | nil => exact fun w hw => Finset.mem_singleton.1 (Finsupp.support_single_subset hw) ▸ h0
  | cons c l ih =>
    intro w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_support_conv hw
    exact hadd x y (hl c List.mem_cons_self x hx) (ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) y hy)

end Conv

section Gen

open Formalism.L2.DIV (Pl kP LevelP)
open GlobalTheory.SymBridge GlobalTheory.LocMod

variable {D : D7} {u : D.what₂.Word}

section At

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Pl D.host.E} (G : GX a ζ₀ PP)

end At

namespace StdSp

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {π : D.host.E} (H : StdSp a ζ₀ π)
include H

end StdSp

section Ker

variable {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

end Ker

end Gen

section World

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.SymBridge Formalism.L2.Forms Formalism.IndefR.Links

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

def chiC (i : ℕ) (P : HeightOneSpectrum (𝓞 B.fields.E)) : (𝓞 B.fields.E ⧸ P.asIdeal)ˣ →* ℂˣ :=
  (Units.map (B.embLL : B.LL →* ℂ)).comp (Formalism.L2.Col.chiP I.Ch P i)

theorem chiC_apply (i P x) : ((chiC I i P x : ℂˣ) : ℂ) = B.embLL ((Formalism.L2.Col.chiP I.Ch P i x : B.LLˣ) : B.LL) := rfl

variable {I l Z}

variable {v : B.Word} {Ch : ℕ → Type} (A : ColDat I l Z v Ch)

variable {a : XPart (I.rec7 l Z) v}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (w : World I l Z) (a : XPart (I.rec7 l Z) v) (o : OffX a k ((B.primes X).vT v)) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

namespace XStdBy

variable {w a o G} {A : ColDat I l Z v (w.C.herm.base.Ch v)} (H : XStdBy w a o G A)
include H

end XStdBy

end World

end GlobalTheory.SeeSaw

end
