module

public import DirectedDistances.PlanarMap.D39PLArcGluing

public section
noncomputable section
namespace DirectedDistances.PlanarMap
namespace Polyline

/-- Helper toward Proposition 5.16: a simple nondegenerate polyline image is
homeomorphic to `[-1,1]`, with its endpoints in the prescribed order. -/
theorem exists_Icc_homeomorph_image (p : Polyline) (hp : p.IsSimple)
    (hpne : p.start ≠ p.finish) :
    ∃ phi : Set.Icc (-1 : ℝ) 1 ≃ₜ ↥p.image,
      (phi ⟨-1, by norm_num⟩ : ℂ) = p.start ∧
        (phi ⟨1, by norm_num⟩ : ℂ) = p.finish := by
  have hlen : 2 ≤ p.points.length := by
    have hpos : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
    by_contra hh
    have hone : p.points.length = 1 := by omega
    have hstart : p.points.length = 1 → p.start = p.finish := by
      intro h
      rcases p with ⟨l, hn⟩
      cases l with
      | nil => simp at h
      | cons a l =>
        cases l with
        | nil => rfl
        | cons b l => simp at h
    exact hpne (hstart hone)
  let e : Set.Icc (-1 : ℝ) 1 ≃ₜ Set.Icc (0 : ℝ) 1 :=
    iccHomeoI (-1 : ℝ) 1 (by norm_num)
  let f : Set.Icc (-1 : ℝ) 1 → p.image := fun t =>
    ⟨p.toPath (e t), by
      rw [← p.range_toPath]
      exact ⟨e t, rfl⟩⟩
  have hf : Continuous f :=
    (p.toPath.continuous.comp e.continuous).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y hxy
    apply e.injective
    exact p.toPath_injective hlen hp (congrArg Subtype.val hxy)
  have hfs : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rw [← p.range_toPath] at hz
    rcases hz with ⟨t, ht⟩
    refine ⟨e.symm t, ?_⟩
    apply Subtype.ext
    change p.toPath (e (e.symm t)) = z
    rw [e.apply_symm_apply]
    exact ht
  let phi : Set.Icc (-1 : ℝ) 1 ≃ₜ ↥p.image :=
    hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfi, hfs⟩)
  have he0 : e ⟨-1, by norm_num⟩ = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    rw [iccHomeoI_apply_coe]
    norm_num
  have he1 : e ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    rw [iccHomeoI_apply_coe]
    norm_num
  refine ⟨phi, ?_, ?_⟩
  · change p.toPath (e ⟨-1, by norm_num⟩) = p.start
    rw [he0]
    simpa using (Path.source p.toPath)
  · change p.toPath (e ⟨1, by norm_num⟩) = p.finish
    rw [he1]
    simpa using (Path.target p.toPath)

/-- Helper toward Proposition 5.16: two simple nondegenerate polyline images
are homeomorphic with the initial and terminal points matched. -/
theorem exists_image_homeomorph_endpoints (p q : Polyline)
    (hp : p.IsSimple) (hq : q.IsSimple)
    (hpne : p.start ≠ p.finish) (hqne : q.start ≠ q.finish) :
    ∃ h : ↥p.image ≃ₜ ↥q.image,
      (h ⟨p.start, Or.inl rfl⟩ : ℂ) = q.start ∧
        (h ⟨p.finish, by
          rw [← p.point_last_eq_finish]
          exact p.point_mem_image (by
            have hpos : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
            omega)⟩ : ℂ) = q.finish := by
  obtain ⟨phi, hphi₀, hphi₁⟩ := p.exists_Icc_homeomorph_image hp hpne
  obtain ⟨psi, hpsi₀, hpsi₁⟩ := q.exists_Icc_homeomorph_image hq hqne
  let x₀ : p.image := ⟨p.start, Or.inl rfl⟩
  let x₁ : p.image := ⟨p.finish, by
    rw [← p.point_last_eq_finish]
    exact p.point_mem_image (by
      have hpos : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
      omega)⟩
  have hx₀ : x₀ = phi ⟨-1, by norm_num⟩ := Subtype.ext hphi₀.symm
  have hx₁ : x₁ = phi ⟨1, by norm_num⟩ := Subtype.ext hphi₁.symm
  let h : p.image ≃ₜ q.image := phi.symm.trans psi
  refine ⟨h, ?_, ?_⟩
  · change (psi (phi.symm x₀) : ℂ) = q.start
    rw [hx₀]
    simpa using hpsi₀
  · change (psi (phi.symm x₁) : ℂ) = q.finish
    rw [hx₁]
    simpa using hpsi₁

/-- Helper toward Proposition 5.16: reversal preserves simplicity and image,
and exchanges the endpoints of a polyline. -/
theorem reverse_preserves_simple_image_endpoints (p : Polyline) (hp : p.IsSimple) :
    p.reverse.IsSimple ∧ p.reverse.image = p.image ∧
      p.reverse.start = p.finish ∧ p.reverse.finish = p.start := by
  exact ⟨isSimple_reverse_transfer p hp, image_reverse_transfer p,
    start_reverse p, finish_reverse p⟩

end Polyline
end DirectedDistances.PlanarMap
end
