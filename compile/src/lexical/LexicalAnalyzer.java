package lexical;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;

/** 
 * 
���ʷ���               �ֱ���                       ���ʷ���                 �ֱ���                        ���ʷ���                �ֱ���       
main        1         char        19          ==        37 
void        2         return      20          {         38
sizeof      3         default     21          }         39
for         4         float       22          (         40
continue    5         short       23          )         41
if          6         typedef     24          "         42(Ӣ����һ����
then        7          ID         25        //  "         43
while       8          NUM        26          '         44
do          9          +          27          ,         46
static      10         -          28          ;         47
int         11         *          29          :         48
double      12         /          30          &         49
struct      13         =          31          \n        50
break       14         %          32          //        51
else        15         <          33        //  **        52
long        16         >          34          /*        53
switch      17         <=         35       (53������)     54  
case        18         >=         36          #         0
str(�����ַ�����       56         ++         55         .          57
 * @author Alice
 *
 **/

public class LexicalAnalyzer {
	//�Ѿ������24���ؼ��֣��ֱ����1��ʼ
	static String[] rwtab=new String[]{"main","void","sizeof","for","continue","if",
		"then","while","do","static","int","double","struct","break","else",
		"long","switch","case","char","return","default","float","short","typedef"}; 

	static String storage="";   //�洢Դ�����ַ���
	static StringBuilder token=new StringBuilder("");  //�洢����������ɵ��ַ���
	static char ch;  //�洢����¶����Դ���򵥸��ַ�
	static int index;  //�������
	static int syn, sum=0; //synΪ�ֱ��룬sumΪ������ASCIIֵ����Ϊʮ������ֵ

	//������
	static void analyzer(){
		token.delete(0, token.length());     //�ÿ�token�������
		ch=storage.charAt(index++);
		while(ch==' '){
			ch=storage.charAt(index++);      //ȥ���ո����
		}
		
		if((ch>='a'&&ch<='z')||(ch>='A'&&ch<='Z')){    //�����ǹؼ��ֻ����Զ���ı�ʶ��
			while((ch>='0'&&ch<='9')||(ch>='a'&&ch<='z')||(ch>='A'&&ch<='Z')){
				token.append(ch);
				ch=storage.charAt(index++);
			}
			index--;      //�˴�ʶ������һ���ַ�δʶ���룬��Ҫ�������ԭ�� 
			syn=25;       //Ĭ��Ϊʶ������ַ���Ϊ�Զ���ı�ʶ�����ֱ���Ϊ25
			String s=token.toString();
			for(int i=0; i<rwtab.length; i++){
				if(s.equals(rwtab[i])){     
					syn=i+1;
					break;    //ʶ����ǹؼ���
				}
			}
		}

		else if((ch>='0'&&ch<='9')){  //ʶ�����������
			sum=0;
			while((ch>='0'&&ch<='9')){
				sum=sum*10+ch-'0';
				ch=storage.charAt(index++);
			}
			index--;   //�˴�ʶ������һ���ַ�δʶ���룬��Ҫ�������ԭ�� 
			syn=26;    //Ĭ��Ϊʶ����������֣��ֱ���Ϊ26
		}

		else switch(ch){
		case '+':
			token.append(ch);
			ch=storage.charAt(index++);
			if(ch=='+'){
				token.append(ch);
				syn=55;
			}
			else{
				syn=27;
				index--;
			}
			break;
		case '-':
			syn=28;
			token.append(ch);
			break;
		case '*':
			token.append(ch);
			ch=storage.charAt(index++);
			if(ch=='*'){
				token.append(ch);
				syn=52;
			}
			else if(ch=='/'){
				token.append(ch);
				syn=54;
			}
			else{
				syn=29;
				index--;
			}
			break;
		case '/':
			token.append(ch);
			ch=storage.charAt(index++);
			if(ch=='/'){
				token.append(ch);
				syn=51;
			}
			else if(ch=='/'){
				while(ch!=' '){
					ch=storage.charAt(index++);  //���Ե�ע�ͣ��Կո�Ϊ�綨
				}
				syn=-2;
				break;
			}
			else if(ch=='*'){
				token.append(ch);
				syn=53;
			}
			else if(ch=='*'){
				while(ch!=' '){
					ch=storage.charAt(index++);  //���Ե�ע�ͣ��Կո�Ϊ�綨
				}
				syn=-2;
				break;
			}
			else{
				syn=30;
				index--;
			}
			break;
		case '%':
			syn=32;
			token.append(ch);
			break;
		case '=':
			token.append(ch);
			ch=storage.charAt(index++);
			if(ch=='='){
				syn=37;
				token.append(ch);
			}
			else{
				syn=31;
				index--;
			}
			break;
		case '<':
			token.append(ch);
			ch=storage.charAt(index++);
			if(ch=='='){
				token.append(ch);
				syn=35;
			}
			else{
				syn=33;
				index--;
			}
			break;
		case '>':
			token.append(ch);
			ch=storage.charAt(index++);
			if(ch=='='){
				token.append(ch);
				syn=36;
			}
			else{
				syn=34;
				index--;
			}
			break;
		case '{':
			syn=38;
			token.append(ch);
			break;
		case '}':
			syn=39;
			token.append(ch);
			break;
		case '(':
			syn=40;
			token.append(ch);
			break;
		case ')':
			syn=41;
			token.append(ch);
			break;
		case '"':
			syn=42;
			token.append(ch);
			break;
		case '\'':    //ʶ�����ţ���˫���Ų���ͬʱ���֣���ͨ��ת���ַ�ʵ��
			syn=44;
			token.append(ch);
			break;
		case ',':
			syn=46;
			token.append(ch);
			break;
		case ';':
			syn=47;
			token.append(ch);
			break;
		case ':':
			syn=48;
			token.append(ch);
			break;
		case '&':
			syn=49;
			token.append(ch);
			break;
		case '#':
			syn=0;
			token.append(ch);
			break;
		case '\\':   //ʶ��\n,����б��ͨ��ת���ַ�ʵ��
			token.append(ch);
			ch=storage.charAt(index++);
			if(ch=='n'){
				token.append(ch);
				syn=50;
			}
			break;
		default:
			syn=-1;
		}
	}

	public void read() throws IOException{  
		String fileName="source.txt";  //��Դ����
		//String fileName="testSR.txt";  //��Դ����
		BufferedReader br=new BufferedReader(new FileReader(fileName));
		String line;
		while((line = br.readLine()) != null){
			storage+=line;
		}
		br.close();
	}

	public void write() throws IOException{
		PrintStream ps=new PrintStream("lexical.txt");  //�����ָ���ļ�
		do{
			analyzer();
			switch(syn){
			case 26:
				ps.println(syn+"\t"+sum); //����
				break;
			case 57:
				ps.println(syn+"\t"+storage.toString());
			case -1:
				break;
			case -2:
				break;
			default:
				ps.println(syn+"\t"+token);
			}
		}while(syn!=0);
		ps.close();
	}

	public static void main(String[] args) throws IOException {
		LexicalAnalyzer la=new LexicalAnalyzer();
		la.read();
		la.write();
	}
}

