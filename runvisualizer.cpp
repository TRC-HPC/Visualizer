#include <iostream>
#include <vector>
#include <cstdlib>
#include <unistd.h>     // fork, execvp, setenv
#include <sys/wait.h>   // waitpid

int main(int argc, char* argv[]) {
    // Use venv if provided, else fall back to python3 on PATH.
    const char* PYTHON = std::getenv("PYTHON_BIN");
    if (!PYTHON) PYTHON = "python3";

    // Script lives next to this executable; run from repo root.
    const char* SCRIPT = "./visualizer_balanced.py";

    // Ensure Python can import from the repo directory.
    setenv("PYTHONPATH", ".", 1);
    setenv("PYTHONUNBUFFERED", "1", 1);

    // Build argv for execvp: [python, script, (files...) , NULL]
    std::vector<char*> args;
    args.push_back(const_cast<char*>(PYTHON));
    args.push_back(const_cast<char*>(SCRIPT));
    for (int i = 1; i < argc; ++i) args.push_back(argv[i]);
    args.push_back(nullptr);

    pid_t pid = fork();
    if (pid < 0) { perror("fork"); return 2; }
    if (pid == 0) {
        execvp(PYTHON, args.data());
        perror("execvp");
        _exit(127);
    }

    int status = 0;
    if (waitpid(pid, &status, 0) < 0) { perror("waitpid"); return 3; }
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    if (WIFSIGNALED(status)) { std::cerr << "Python terminated by signal " << WTERMSIG(status) << "\n"; return 128 + WTERMSIG(status); }
    std::cerr << "Python ended unexpectedly\n";
    return 4;
}
