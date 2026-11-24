using Documenter, PracticalCAS

makedocs(
    sitename = "PracticalCAS.jl",
    modules = [PracticalCAS],
    format = Documenter.HTML(prettyurls = get(ENV, "CI", "false") == "true"),
    pages = ["Home" => "index.md", "API" => "api.md"],
    checkdocs = :exports,
    warnonly = [:missing_docs, :cross_references],
)

deploydocs(repo = "github.com/EvoArt/PracticalCAS.jl.git", devbranch = "main")
