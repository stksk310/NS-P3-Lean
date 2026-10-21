import NSP3.Certified322Row22
import NSP3.IndexedSliceCoverage
namespace NSP3
def checked322Rows : List CertificateRow :=
  checkedCertificateRows ++ [certificate322Row20,certificate322Row21,certificate322Row22]
theorem checked322Rows_checked : ∀ row ∈ checked322Rows, certificateRowCheck row = true := by
  intro row hr
  simp only [checked322Rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr
  · exact (List.all_eq_true.mp checked_certificateRows_checked) row hr
  · subst row; exact certificate322Row20_checked
  · subst row; exact certificate322Row21_checked
  · subst row; exact certificate322Row22_checked
end NSP3
