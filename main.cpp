
#include "basis_pms.h"

#include "settings.h"
#include "cmdline.h"
#include "parse_arguments.h"

#include <sstream>
#include <string>

//extern long long total_step;

void interrupt(int sig)
{
	print_best_solution();
	free_memory();
	exit(10);
}

int main(int argc, char *argv[])
{
    signal(SIGINT, interrupt);
    signal(SIGTERM, interrupt);
    signal(SIGILL, interrupt);

	default_algorithm_settings();
	Config cfg;
	if(!parse_args(argc, argv, cfg))
	{
		cout << "parse args failed." << endl;
		return -1;
	}

    try {
        srand((unsigned) time(NULL));
        start_timing();
        signal(SIGTERM, interrupt);

        path = cfg.input_file;
        vector<int> init_solution;
        build_instance(cfg.input_file.c_str());
        settings();
        parse_arguments(argc, argv);
        local_search(init_solution, cfg.input_file.c_str());

        print_best_solution();
        free_memory();
    }
    catch (const char* msg) {
        ofstream ofile("error.log");
        ofile << path << " " << msg << endl;
        ofile.close();
        exit(-1);
    }
	return 0;
}
