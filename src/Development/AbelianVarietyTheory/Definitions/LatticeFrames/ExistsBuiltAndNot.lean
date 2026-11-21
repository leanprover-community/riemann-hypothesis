import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BuiltGIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Core.AtG.BuiltModel

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}

theorem under_inj (u : B.Word) (P Q : (B.primes X).vT u)
    (e : P.1.under (𝓞 B.host.F) = Q.1.under (𝓞 B.host.F)) : P = Q := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hc := GlobalTheory.MuOffMove.conjP_notMem_vT hPr P.2
  have hsp := (split_of_conj_ne₂ B.fields P.1 (P.1.under (𝓞 B.host.F)) hX (fun e => hc (e.symm ▸ P.2)) rfl).2
  refine Subtype.ext (((hsp Q.1).1 (congrArg HeightOneSpectrum.asIdeal e.symm)).resolve_right fun e' => hc (e' ▸ Q.2)).symm

def errOf (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) : ErrX (I.rec7 l Z) where
  piG := X.piG
  piG_K := X.piG_K
  piG_norm := X.piG_norm
  piT := X.piT
  piT_K := X.piT_K
  piT_norm := X.piT_norm
  piT_cong u := Ideal.mem_span_singleton.2 (X.piT_cong u)
  vPl u (P : (B.primes X).vT u) := P.1.under (𝓞 B.host.F)
  vPl_inj u := under_inj u
  norm_mem_place_ideal u (P : (B.primes X).vT u) :=
    (GlobalTheory.MuOffMove.natCast_mem_under (X := B.fields) P.1 (B.T u)).2 (T_mem (base_fields_primes_ok B X).2.1 u P)



theorem cong {D : D7} {EX : ErrX D} (h : BuiltG D EX) (i : Fin 2) :
    ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∣ EX.piG i - 1 :=
  builtG_ind (Q := fun D EX => ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∣ EX.piG i - 1)
    (fun _ X _ _ _ _ _ _ EX e => by rw [e]; exact X.piG_cong i) h



def negG {D : D7} (EX : ErrX D) : ErrX D :=
  { EX with
    piG := fun i => -EX.piG i
    piG_K := fun i => by simpa using neg_mem (EX.piG_K i)
    piG_norm := fun i => by simpa using EX.piG_norm i }



end GlobalTheory.Core.AtG.BuiltModel

end
