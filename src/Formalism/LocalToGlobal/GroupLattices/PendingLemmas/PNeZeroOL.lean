module

public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.CloudBound
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainK
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ConditionIffAdditiveMaps
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.FrobeniusSqIterateTeichmuller

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem
open scoped TensorProduct

namespace Formalism.L2.G.Pend

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Chain

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) {LL : Type} [Field LL] (e : LL →+* G.Kf) (m : ℕ)
  (V : ℕ → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module LL (V j)] (ix : ℕ → Type) (b : ∀ j, Module.Basis (ix j) LL (V j))
  (cmp : ∀ j, V j →ₛₗ[e] Lv.Fm j) (li : ∀ j, j ≤ m → LinearIndependent G.Kf fun a => cmp j (b j a))
  (KL : ∀ j, V j →ₗ[LL] V (j + 1))

end Chain

section Ring

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (L : IntermediateField (KO p n) (Om p n)) [FiniteDimensional (KO p n) L]

end Ring

section Record

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)

end Record

section Record2

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)

variable (Lv : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc)) (Ch : Chain Lv)
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (hfin : ∀ j c', (Lv.lev j c').FinClasses)

end Record2

section Record3

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (Lv : Levels (fillsL D u h L h5 h2 he r Lc I ψ e c hc)) (Ch : Chain Lv)
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k) (hfin : ∀ j c', (Lv.lev j c').FinClasses) (hst : FinStab Lv)

end Record3

section ChainF

variable {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) {D : D7} (Tw : TwForms D) (u : D.what₂.Word)
  (w : D.what₂.places.Pl) (eL : D.what₂.LL →+* G.Kf)
  (cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[eL] Lv.Fm j)
  (li : ∀ j, j ≤ D.R.m → LinearIndependent G.Kf fun a => cmp j (((Tw.fm u (D.what₂.muAt w)).lat j).b a))

end ChainF

end Formalism.L2.G.Pend
