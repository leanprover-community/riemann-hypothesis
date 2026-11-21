import Formalism.LocalToGlobal.Columns.DetChrOfChi
import Formalism.LocalToGlobal.Columns.Target

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def ChiReads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word) : Prop :=
  ∀ j (cl : StCl W Λ u j), ∃ y : D.Dt,
    ((D.chiD y : ℂˣ) : ℂ) = σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) ∧
      K.idl (QuotientGroup.mk y) = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (R.N j)) (K.seam.lat (repN W Λ u j cl))



section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem carries_globLat (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    Formalism.L2.Herm.Carries g (stdLat E n) (Formalism.UG.CS.globLat g (stdLat E n)) := fun x =>
  Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.csGlob_intAdApprox F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top g x

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hlat := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

section Rep

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)



end Rep

section Rel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def RelReads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word) : Prop :=
  ∀ j (cl : StCl W Λ u j), ∃ y : D.Dt,
    ((D.chiD y : ℂˣ) : ℂ) = σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) ∧
      ∃ L L' : SDLat D.host.E (R.N j), L.1 = StandardLatticesGL3.stdL D (R.N j) ∧ L'.1 = K.seam.lat (repN W Λ u j cl) ∧
        (QuotientGroup.mk y : D.Dt ⧸ D.UO) = D.relDet (R.N j) L L'



end Rel

end DetChrChi

end Formalism.L2.Col
