extern int a;
extern int b;

int res[3];

int circ() {

	int output=0; // -1 failes
	int i;
	for(i=0; i < 3;i++) {
		res[i] = i*i;
	} 
	for(i=0; i < 3;i++) {
		if (res[i] <= a*b) {
			output = i;
		}
	} 
	return output;
/*	res = (a != b) ? 1 : 0;
	if(res && !a) {
		res = 0;
	}
	return res;*/
}


void main() {
 a = circ();
}
