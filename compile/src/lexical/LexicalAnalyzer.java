package lexical;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;

/** 
 * 
单词符号               种别码                       单词符号                 种别码                        单词符号                种别码       
main        1         char        19          ==        37 
void        2         return      20          {         38
sizeof      3         default     21          }         39
for         4         float       22          (         40
continue    5         short       23          )         41
if          6         typedef     24          "         42(英文下一样）
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
switch      17         <=         35       (53反过来)     54  
case        18         >=         36          #         0
str(代表字符串）       56         ++         55         .          57
 * @author Alice
 *
 **/

public class LexicalAnalyzer {
	//已经定义的24个关键字，种别码从1开始
	static String[] rwtab=new String[]{"main","void","sizeof","for","continue","if",
		"then","while","do","static","int","double","struct","break","else",
		"long","switch","case","char","return","default","float","short","typedef"}; 

	static String storage="";   //存储源程序字符串
	static StringBuilder token=new StringBuilder("");  //存储单词自身组成的字符串
	static char ch;  //存储最近新读入的源程序单个字符
	static int index;  //计量标记
	static int syn, sum=0; //syn为种别码，sum为从数字ASCII值换算为十进制数值

	//分析器
	static void analyzer(){
		token.delete(0, token.length());     //置空token对象，清除
		ch=storage.charAt(index++);
		while(ch==' '){
			ch=storage.charAt(index++);      //去除空格符号
		}
		
		if((ch>='a'&&ch<='z')||(ch>='A'&&ch<='Z')){    //可能是关键字或者自定义的标识符
			while((ch>='0'&&ch<='9')||(ch>='a'&&ch<='z')||(ch>='A'&&ch<='Z')){
				token.append(ch);
				ch=storage.charAt(index++);
			}
			index--;      //此次识别的最后一个字符未识别入，需要将标记退原处 
			syn=25;       //默认为识别出的字符串为自定义的标识符，种别码为25
			String s=token.toString();
			for(int i=0; i<rwtab.length; i++){
				if(s.equals(rwtab[i])){     
					syn=i+1;
					break;    //识别出是关键字
				}
			}
		}

		else if((ch>='0'&&ch<='9')){  //识别出的是数字
			sum=0;
			while((ch>='0'&&ch<='9')){
				sum=sum*10+ch-'0';
				ch=storage.charAt(index++);
			}
			index--;   //此次识别的最后一个字符未识别入，需要将标记退原处 
			syn=26;    //默认为识别出的是数字，种别码为26
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
					ch=storage.charAt(index++);  //忽略掉注释，以空格为界定
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
					ch=storage.charAt(index++);  //忽略掉注释，以空格为界定
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
		case '\'':    //识别单引号，因单双引号不能同时出现，故通过转义字符实现
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
		case '\\':   //识别\n,反单斜杠通过转义字符实现
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
		String fileName="source.txt";  //读源程序
		//String fileName="testSR.txt";  //读源程序
		BufferedReader br=new BufferedReader(new FileReader(fileName));
		String line;
		while((line = br.readLine()) != null){
			storage+=line;
		}
		br.close();
	}

	public void write() throws IOException{
		PrintStream ps=new PrintStream("lexical.txt");  //输出到指定文件
		do{
			analyzer();
			switch(syn){
			case 26:
				ps.println(syn+"\t"+sum); //数字
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

